(** * A box to prevent timing side channels (part of TCB) *)
Require Import FunctionApp Coq.Program.Basics Coq.Numbers.Natural.Peano.NPeano.

Local Open Scope program_scope.

Set Implicit Arguments.

(** ** Summary

    We implement a box that passes information between other boxes in
    a way that partially or completely obscures timing side-channels:

<<
                  System Clock (tick)
                           │
                           ↓
    notify change     ┌──────────┐
    --------------->  │          │
                      │          │
    publish value     │          │
      (data in)       │ Tick Box │ -----> publish update (data out)
    --------------->  │          │
                      │          │
    <---------------  │          │
     request update   └──────────┘

>>

    The Tick Box implements a kind of wrapper around what can be
    thought of as a single mutable cell, which is expensive to
    compute.

    ** Example

    Suppose you have an encryption box, and you want to publish
    updates to data via the encryption box in a timing-oblivious way.
    To do this, you hook the encryption box up to a Tick Box.

    Every [X] ticks, if there has been a notified change in the last
    [Y] ticks, or if the last published value is out of date, the Tick
    Box will publish its current value, and then, [Z] ticks later,
    request an updated value from the encryption box.  The encryption
    box should construct a unique encryption (using its own source of
    randomness), and raise the "publish value (data in)" event with
    that new value.  We must have [Z < X].

    The tick box will emit a warning if it has not recieved a "publish
    value (data in)" event after its most recent request when it is
    time to publish an update.  In this case, we will defer publishing
    an update of our value, leaking timing information.  (Leaking
    information through timing is unavoidable in this case.)

    The tick box will emit a separate warning if it detects that the
    program is being insufficiently responsive, and that the number of
    ticks between publishes is different from [X] by at least [W].

    ** Configurable parameters

    - [publishInterval] ([X] above) - the number of ticks to wait
      between successive publishings.  A value of [0] means to publish
      as soon as the number of ticks increments.

    - [publishDuration] ([Y] above) - the number of [PublishInterval]s
      after the most recent change to continue publishing updates.  A
      value of [0] means to publish at most once for each change.  A
      special flag value of [∞] means to always publish.

    - [waitBeforeUpdateInterval] ([Z] above) - the number of ticks to
      wait after a publish before requesting an update.

    - [publishPrecision] ([W] above) - Suppose the clock does not
      publish on every tick, and we find that, previously, we were
      given tick [X₀ < X], and on the current update, we are given [X₁
      > X].  We will emit a warning iff [X₁ - X > W + 1].


    Note: Setting [publishInterval] and [waitBeforeUpdateInterval] are
          privlidged operations: if [publishInterval] is too low
          relative to [waitBeforeUpdateInterval], then there will not
          be time to complete the computation between successive
          publishes, and timing information will be leaked.

          Similarly, if [PublishDuration] is set to any value other
          than [∞], a controlled amount of timing information is
          leaked.

    TODO: Do we want to publish in multiples of [X] according to the
          system clock, or do we want to publish [X] ticks after
          whenever the last time we managed to publish was?
          Currently, we do the latter.

    TODO: Implement the optimization where we ask to shut off tick
          notifications if we haven't seen updates recently. *)

(** We implement the following state machine:

<<

                         ┌───────────────┐     Notify Change       ┌───────────────────┐
                         │ initial state │───────────────────────> │ initially waiting │
                         │     no data   │  Fire: Request Update   │      on data      │
                         └───────────────┘                         └───────────────────┘
                                        ^                                   │
                                        |                                   │
                +--------------------+  |                                   │
                | Ready to publish?  |  |                                   │ Data Ready
                +--------------------+  |                                   │
             Yes |         |        ^   |                                   │
   Fire: Warning |      No |   Tick │   |                                   │
                 V         V        │   |                                   V
                ┌────────────────────┐  |                          ┌───────────────────┐ ───┐ Tick to ≤ X
  Notify Change │                    │  |      Data Ready          │                   │ <──┘
   ┌─────────── │  waiting on data   │ ──────────────────────────> │     have data     │
   └──────────> │                    │  |                          │                   │ ───┐ Notify Change
reset publishes └────────────────────┘  |                          └───────────────────┘ <──┘ reset publishes to 0
to 0                      ^             |                                   │
                          │             |                                   │
                          │             |                                   │
               Fire:      │ Tick to ≥ Z |                                   │
           Request Update │             |                                   │
                          │             |                                   │
                          │             |                                   │
                          │    Tick to  |                                   │
                          │     < Z     |                                   │
                          │   ┌─────┐   |                                   │
                          │   │     │   |                                   │
                          │   V     │   |                                   │
                ┌────────────────────┐  |                                   │
  Notify Change │                    │  |                                   │
   ┌─────────── │  waiting on ticks  │  |                                   │
   └──────────> │                    │  |                                   │
reset publishes └────────────────────┘  |                                   │
to 0                      ^             |                                   │
                          |             |                                   │ Tick to > X
                          | No          | Yes                               │ Fire: Transmit Data
                          |             |                                   V
                         +-----------------------+      No         +-------------------+
                         |                       | <-------------  |                   |
                         |   Enough Publishes?   |                 | Ticks too coarse? |
                         |                       |      Yes        |                   |
                         +-----------------------+ <-------------  +-------------------+
                                                    Fire: Warning
>> *)

Inductive PublishDurationT := durationOf (n : nat) | inf.
Bind Scope duration_scope with PublishDurationT.
Delimit Scope duration_scope with duration.
Notation "∞" := inf : duration_scope.
Coercion durationOf : nat >-> PublishDurationT.
Local Open Scope duration_scope.
Local Open Scope bool_scope.

Definition duration_leb (x : nat) (y : PublishDurationT) : bool :=
  match y with
    | durationOf y' => x <=? y'
    | inf => true
  end.

Infix "<=?" := duration_leb : duration_scope.

Notation "x >? y" := (y <? x) (at level 70, right associativity) : nat_scope.
Notation "x >=? y" := (y <=? x) (at level 70, right associativity) : nat_scope.

Section trustedTickBox.
  Variable dataT : Type.

  Inductive TickBoxPreState :=
  | NoData
  | InitiallyWaitingOnData
  | HaveData (data : dataT) (ticks : nat) (publishesSinceLastChange : option nat)
  | WaitingOnData (ticks : nat) (publishesSinceLastChange : option nat)
  | WaitingOnTicks (ticks : nat) (publishesSinceLastChange : option nat).

  Record TickBoxState :=
    {
      curData :> TickBoxPreState;
      publishInterval : nat;
      publishDuration : PublishDurationT;
      waitBeforeUpdateInterval : nat;
      publishPrecision : nat
    }.

(* python:
<<
fields=[(x.strip(), y.strip()) for x, y in [z.split(':') for z in """
      curData : TickBoxPreState;
      publishInterval : nat;
      publishDuration : PublishDurationT;
      waitBeforeUpdateInterval : nat;
      publishPrecision : nat""".split(';')]]
for field0, ty0 in fields:
    body = ';\n          '.join((('%s := st.(%s)' % (field, field)) if field != field0 else ('%s := v' % field))
                                for field, ty in fields)
    print('  Definition set_%s (st : TickBoxState) (v : %s)' % (field0, ty0))
    print('    := {| ' + body + ' |}.\n')
>> *)

  Definition set_curData (st : TickBoxState) (v : TickBoxPreState)
    := {| curData := v;
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          waitBeforeUpdateInterval := st.(waitBeforeUpdateInterval);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_publishInterval (st : TickBoxState) (v : nat)
    := {| curData := st.(curData);
          publishInterval := v;
          publishDuration := st.(publishDuration);
          waitBeforeUpdateInterval := st.(waitBeforeUpdateInterval);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_publishDuration (st : TickBoxState) (v : PublishDurationT)
    := {| curData := st.(curData);
          publishInterval := st.(publishInterval);
          publishDuration := v;
          waitBeforeUpdateInterval := st.(waitBeforeUpdateInterval);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_waitBeforeUpdateInterval (st : TickBoxState) (v : nat)
    := {| curData := st.(curData);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          waitBeforeUpdateInterval := v;
          publishPrecision := st.(publishPrecision) |}.

  Definition set_publishPrecision (st : TickBoxState) (v : nat)
    := {| curData := st.(curData);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          waitBeforeUpdateInterval := st.(waitBeforeUpdateInterval);
          publishPrecision := v |}.

  Inductive tbConfigInput :=
  | tbSetPublishInterval (_ : nat)
  | tbSetPublishDuration (_ : PublishDurationT)
  | tbSetWaitBeforeUpdateInterval (_ : nat)
  | tbSetPublishPrecision (_ : nat).

  Inductive tbEventInput :=
  | tbNotifyChange
  | tbTick (addedTickCount : nat)
  | tbValueReady (val : dataT).

  Inductive tbWarningOutput :=
  | tbWarnNoDataReady
  | tbWarnTicksTooInfrequent
  | tbWarnInvalidWaitBeforeUpdateInterval (_ : nat)
  | tbWarnInvalidEvent (st : TickBoxPreState) (ev : tbEventInput).

  Inductive tbEventOutput :=
  | tbRequestDataUpdate
  | tbPublishUpdate (val : dataT).

  Definition tbInput := (tbConfigInput + tbEventInput)%type.
  Definition tbOutput := (tbWarningOutput + tbEventOutput)%type.

  Context (world : Type)
          (handle : tbOutput -> action world).

  Definition initState : TickBoxState :=
    {| curData := NoData;
       publishInterval := 0;
       publishDuration := ∞;
       waitBeforeUpdateInterval := 0;
       publishPrecision := 0 |}.

  Definition readyToTransmit (ticks : nat) (st : TickBoxState) : bool :=
    ticks >? st.(publishInterval).

  Definition readyToGetUpdate (ticks : nat) (st : TickBoxState) : bool :=
    ticks >? st.(waitBeforeUpdateInterval).

  Definition invalidWaitBeforeUpdateInterval (val : nat) (st : TickBoxState) : bool :=
    val >? st.(publishInterval).

  (** Should we emit a warning about [tbTick] not being called often
      enough? *)
  Definition ticksTooCoarse (ticks : nat) (st : TickBoxState) : bool :=
    ticks - st.(publishInterval) >? st.(publishPrecision) + 1.

  (** Should we emit a warning about [tbTick] not being called often
      enough, when we're waiting to request an update? *)
  Definition ticksTooCoarseWaitingOnTicks (ticks : nat) (st : TickBoxState) : bool :=
    ticks - st.(waitBeforeUpdateInterval) >? st.(publishPrecision) + 1.

  (** Have we transmitted enough times since the last change to sleep? *)
  Definition enoughTransmissions (publishesSinceLastChange : nat) (st : TickBoxState) : bool :=
    negb (publishesSinceLastChange <=? st.(publishDuration)).

  Definition tickBoxLoopBody
             (tickBoxLoop : TickBoxState -> process tbInput world)
             (st : TickBoxState)
  : tbInput -> action world * process tbInput world
    := fun i =>
         match i, st.(curData) with

           | inl (tbSetPublishInterval val), _
             => (id, tickBoxLoop (set_publishInterval st val))

           | inl (tbSetWaitBeforeUpdateInterval val), _
             => if invalidWaitBeforeUpdateInterval val st
                then (handle (inl (tbWarnInvalidWaitBeforeUpdateInterval val)), tickBoxLoop st)
                else (id, tickBoxLoop (set_waitBeforeUpdateInterval st val))

           | inl (tbSetPublishDuration val), _
             => (id, tickBoxLoop (set_publishDuration st val))

           | inl (tbSetPublishPrecision val), _
             => (id, tickBoxLoop (set_publishPrecision st val))

           | inr tbNotifyChange, NoData
             => (handle (inr tbRequestDataUpdate), tickBoxLoop (set_curData st InitiallyWaitingOnData))

           | inr tbNotifyChange, HaveData data ticks publishesSinceLastChange
             => (id, tickBoxLoop (set_curData st (HaveData data ticks None)))

           | inr tbNotifyChange, WaitingOnData ticks publishesSinceLastChange
             => (id, tickBoxLoop (set_curData st (WaitingOnData ticks None)))

           | inr tbNotifyChange, WaitingOnTicks ticks publishesSinceLastChange
             => (id, tickBoxLoop (set_curData st (WaitingOnTicks ticks None)))

           | inr tbNotifyChange, InitiallyWaitingOnData
             => (id, tickBoxLoop st)

           | inr (tbValueReady data), InitiallyWaitingOnData
             => (id, tickBoxLoop (set_curData st (HaveData data 0 (Some 0))))

           | inr (tbValueReady data), WaitingOnData ticks publishesSinceLastChange
             => (id, tickBoxLoop (set_curData st (HaveData data ticks publishesSinceLastChange)))

           | inr (tbValueReady data), HaveData _ _ _
             => (handle (inl (tbWarnInvalidEvent st.(curData) (tbValueReady data))), tickBoxLoop st)

           | inr (tbValueReady data), NoData
             => (handle (inl (tbWarnInvalidEvent st.(curData) (tbValueReady data))), tickBoxLoop st)

           | inr (tbValueReady data), WaitingOnTicks _ _
             => (handle (inl (tbWarnInvalidEvent st.(curData) (tbValueReady data))), tickBoxLoop st)

           | inr (tbTick ticksSinceLastTbTick), NoData
             => (id, tickBoxLoop st)

           | inr (tbTick ticksSinceLastTbTick), InitiallyWaitingOnData
             => (id, tickBoxLoop st)

           | inr (tbTick ticksSinceLastTbTick), HaveData data ticks publishesSinceLastChange
             => let ticks' := ticksSinceLastTbTick + ticks in
                let st' := set_curData st (HaveData data ticks' publishesSinceLastChange) in
                let publishesSinceLastChange' := match publishesSinceLastChange with
                                                   | None => 0
                                                   | Some n => n + 1
                                                 end in
                let actions := handle (inr (tbPublishUpdate data)) in
                let actions := (if ticksTooCoarse ticks' st'
                                then actions ∘ handle (inl tbWarnTicksTooInfrequent)
                                else actions) in
                (actions,
                 (if enoughTransmissions publishesSinceLastChange' st'
                  then tickBoxLoop (set_curData st NoData)
                  else tickBoxLoop (set_curData st (WaitingOnTicks 0 (Some publishesSinceLastChange')))))

           | inr (tbTick ticksSinceLastTick), WaitingOnTicks ticks publishesSinceLastChange
             => let ticks' := ticksSinceLastTick + ticks in
                let st_request := set_curData st (WaitingOnData ticks' publishesSinceLastChange) in
                let st_waiting := set_curData st (WaitingOnTicks ticks' publishesSinceLastChange) in
                let actions := (if ticksTooCoarseWaitingOnTicks ticks' st
                                then handle (inl tbWarnTicksTooInfrequent)
                                else id) in
                if readyToGetUpdate ticks' st
                then (actions ∘ handle (inr tbRequestDataUpdate), tickBoxLoop st_request)
                else (actions, tickBoxLoop st_waiting)

           | inr (tbTick ticksSinceLastTick), WaitingOnData ticks publishesSinceLastChange
             => let ticks' := ticks + ticksSinceLastTick in
                ((if readyToTransmit ticks' st
                  then handle (inl tbWarnNoDataReady)
                  else id),
                 tickBoxLoop (set_curData st (WaitingOnData ticks' publishesSinceLastChange)))

         end.

  CoFixpoint tickBoxLoop (st : TickBoxState) :=
    Step (tickBoxLoopBody tickBoxLoop st).

  Definition tickBox : process _ _ := tickBoxLoop initState.
End trustedTickBox.
