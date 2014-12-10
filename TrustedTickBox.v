(** * A box to prevent timing side channels (part of TCB) *)
Require Import Coq.Program.Basics Coq.NArith.NArith Coq.Lists.List.

Require Import FunctionApp.

Set Implicit Arguments.

Local Open Scope list_scope.
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

              Tick mod X ┌───────────────┐     Notify Change       ┌───────────────────┐
              ┌───────── │ initial state │───────────────────────> │ initially waiting │ ───┐ Tick mod X
              └────────> │     no data   │  Fire: Request Update   │      on data      │ <──┘
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

Inductive PublishDurationT := durationOf (n : N) | inf.
Bind Scope duration_scope with PublishDurationT.
Delimit Scope duration_scope with duration.
Notation "∞" := inf : duration_scope.
Coercion durationOf : N >-> PublishDurationT.
Local Open Scope duration_scope.
Local Open Scope bool_scope.
Local Open Scope N_scope.

Definition duration_leb (x : N) (y : PublishDurationT) : bool :=
  match y with
    | durationOf y' => x <=? y'
    | inf => true
  end.

Infix "<=?" := duration_leb : duration_scope.
Local Open Scope duration_scope.

Notation "x >? y" := (y <? x) (at level 70, right associativity) : N_scope.
Notation "x >=? y" := (y <=? x) (at level 70, right associativity) : N_scope.

Section trustedTickBox.
  Variable dataT : Type.

  Inductive TickBoxPreState :=
  | NoData (ticks : N)
  | InitiallyWaitingOnData (ticks : N)
  | HaveData (ticks : N) (data : dataT) (publishesSinceLastChange : option N)
  | WaitingOnData (ticks : N) (publishesSinceLastChange : option N)
  | WaitingOnTicks (ticks : N) (publishesSinceLastChange : option N).

  Record TickBoxState :=
    {
      curData :> TickBoxPreState;
      publishInterval : N;
      publishDuration : PublishDurationT;
      waitBeforeUpdateInterval : N;
      publishPrecision : N
    }.

(* python:
<<
fields=[(x.strip(), y.strip()) for x, y in [z.split(':') for z in """
      curData : TickBoxPreState;
      publishInterval : N;
      publishDuration : PublishDurationT;
      waitBeforeUpdateInterval : N;
      publishPrecision : N""".split(';')]]
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

  Definition set_publishInterval (st : TickBoxState) (v : N)
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

  Definition set_waitBeforeUpdateInterval (st : TickBoxState) (v : N)
    := {| curData := st.(curData);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          waitBeforeUpdateInterval := v;
          publishPrecision := st.(publishPrecision) |}.

  Definition set_publishPrecision (st : TickBoxState) (v : N)
    := {| curData := st.(curData);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          waitBeforeUpdateInterval := st.(waitBeforeUpdateInterval);
          publishPrecision := v |}.

  Inductive tbConfigInput :=
  | tbSetPublishInterval (_ : N)
  | tbSetPublishDuration (_ : PublishDurationT)
  | tbSetWaitBeforeUpdateInterval (_ : N)
  | tbSetPublishPrecision (_ : N).

  Inductive tbEventInput :=
  | tbNotifyChange
  | tbTick (addedTickCount : N)
  | tbValueReady (val : dataT).

  Inductive tbWarningOutput :=
  | tbWarnNoDataReady
  | tbWarnTicksTooInfrequent
  | tbWarnInvalidWaitBeforeUpdateInterval (_ : N)
  | tbWarnInvalidEvent (st : TickBoxPreState) (ev : tbEventInput).

  Inductive tbEventOutput :=
  | tbRequestDataUpdate
  | tbPublishUpdate (val : dataT).

  Definition tbInput := (tbConfigInput + tbEventInput)%type.
  Definition tbOutput := (tbWarningOutput + tbEventOutput)%type.

  Context (world : Type)
          (handle : tbOutput -> action world).

  Definition initState : TickBoxState :=
    {| curData := NoData 0;
       publishInterval := 10000000000;
       publishDuration := ∞;
       waitBeforeUpdateInterval := 8000000000;
       publishPrecision := 0 |}.

  Definition readyToTransmit (ticks : N) (st : TickBoxState) : bool :=
    ticks >? st.(publishInterval).

  Definition readyToGetUpdate (ticks : N) (st : TickBoxState) : bool :=
    ticks >? st.(waitBeforeUpdateInterval).

  Definition invalidWaitBeforeUpdateInterval (val : N) (st : TickBoxState) : bool :=
    val >? st.(publishInterval).

  (** Should we emit a warning about [tbTick] not being called often
      enough? *)
  Definition ticksTooCoarse (ticks : N) (st : TickBoxState) : bool :=
    ticks - st.(publishInterval) >? st.(publishPrecision) + 1.

  (** Should we emit a warning about [tbTick] not being called often
      enough, when we're waiting to request an update? *)
  Definition ticksTooCoarseWaitingOnTicks (ticks : N) (st : TickBoxState) : bool :=
    ticks - st.(waitBeforeUpdateInterval) >? st.(publishPrecision) + 1.

  (** Have we transmitted enough times since the last change to sleep? *)
  Definition enoughTransmissions (publishesSinceLastChange : N) (st : TickBoxState) : bool :=
    negb (publishesSinceLastChange <=? st.(publishDuration)).

  Definition ticksMod (ticks : N) (st : TickBoxState)
  : N
    := N.modulo ticks st.(publishInterval).

  Definition tickBoxLoopPreBody
             (st : TickBoxState)
  : tbInput -> (list tbOutput) * TickBoxState
    := fun i =>
         match i, st.(curData) with

           | inl (tbSetPublishInterval val), _
             => (nil, set_publishInterval st val)

           | inl (tbSetWaitBeforeUpdateInterval val), _
             => if invalidWaitBeforeUpdateInterval val st
                then ((inl (tbWarnInvalidWaitBeforeUpdateInterval val))::nil, st)
                else (nil, set_waitBeforeUpdateInterval st val)

           | inl (tbSetPublishDuration val), _
             => (nil, set_publishDuration st val)

           | inl (tbSetPublishPrecision val), _
             => (nil, set_publishPrecision st val)

           | inr tbNotifyChange, NoData ticks
             => ((inr tbRequestDataUpdate)::nil, set_curData st (InitiallyWaitingOnData ticks))

           | inr tbNotifyChange, HaveData ticks data publishesSinceLastChange
             => (nil, set_curData st (HaveData ticks data None))

           | inr tbNotifyChange, WaitingOnData ticks publishesSinceLastChange
             => (nil, set_curData st (WaitingOnData ticks None))

           | inr tbNotifyChange, WaitingOnTicks ticks publishesSinceLastChange
             => (nil, set_curData st (WaitingOnTicks ticks None))

           | inr tbNotifyChange, InitiallyWaitingOnData ticks
             => (nil, st)

           | inr (tbValueReady data), InitiallyWaitingOnData ticks
             => (nil, set_curData st (HaveData ticks data (Some 0)))

           | inr (tbValueReady data), WaitingOnData ticks publishesSinceLastChange
             => (nil, set_curData st (HaveData ticks data publishesSinceLastChange))

           | inr (tbValueReady data), HaveData _ _ _
             => ((inl (tbWarnInvalidEvent st.(curData) (tbValueReady data)))::nil, st)

           | inr (tbValueReady data), NoData ticks
             => ((inl (tbWarnInvalidEvent st.(curData) (tbValueReady data)))::nil, st)

           | inr (tbValueReady data), WaitingOnTicks _ _
             => ((inl (tbWarnInvalidEvent st.(curData) (tbValueReady data)))::nil, st)

           | inr (tbTick ticksSinceLastTbTick), NoData ticks
             => (nil, set_curData st (NoData (ticksMod (ticks + ticksSinceLastTbTick) st)))

           | inr (tbTick ticksSinceLastTbTick), InitiallyWaitingOnData ticks
             => (nil, set_curData st (InitiallyWaitingOnData (ticksMod (ticks + ticksSinceLastTbTick) st)))

           | inr (tbTick ticksSinceLastTbTick), HaveData ticks data publishesSinceLastChange
             => let ticks' := ticksSinceLastTbTick + ticks in
                let st' := set_curData st (HaveData ticks' data publishesSinceLastChange) in
                let publishesSinceLastChange' := match publishesSinceLastChange with
                                                   | None => 0
                                                   | Some n => n + 1
                                                 end in
                let actions := (inr (tbPublishUpdate data))::nil in
                let actions := (if ticksTooCoarse ticks' st'
                                then (inl tbWarnTicksTooInfrequent)::actions
                                else actions) in
                (actions,
                 (if enoughTransmissions publishesSinceLastChange' st'
                  then (set_curData st (NoData (ticksMod ticks' st')))
                  else (set_curData st (WaitingOnTicks (ticksMod ticks' st') (Some publishesSinceLastChange')))))

           | inr (tbTick ticksSinceLastTick), WaitingOnTicks ticks publishesSinceLastChange
             => let ticks' := ticksSinceLastTick + ticks in
                let st_request := set_curData st (WaitingOnData ticks' publishesSinceLastChange) in
                let st_waiting := set_curData st (WaitingOnTicks ticks' publishesSinceLastChange) in
                let actions := (if ticksTooCoarseWaitingOnTicks ticks' st
                                then (inl tbWarnTicksTooInfrequent)::nil
                                else nil) in
                if readyToGetUpdate ticks' st
                then ((inr tbRequestDataUpdate)::actions, st_request)
                else (actions, st_waiting)

           | inr (tbTick ticksSinceLastTick), WaitingOnData ticks publishesSinceLastChange
             => let ticks' := ticks + ticksSinceLastTick in
                ((if readyToTransmit ticks' st
                  then (inl tbWarnNoDataReady)::nil
                  else nil),
                 set_curData st (WaitingOnData ticks' publishesSinceLastChange))

         end.

  Definition tickBoxLoopBody {T}
             (tickBoxLoop : TickBoxState -> T)
             (st : TickBoxState)
  : tbInput -> action world * T
    := fun i => let outputs := fst (tickBoxLoopPreBody st i) in
                let st' := snd (tickBoxLoopPreBody st i) in
                (fold_left compose (map handle outputs) id,
                 tickBoxLoop st').


  CoFixpoint tickBoxLoop (st : TickBoxState) :=
    Step (tickBoxLoopBody tickBoxLoop st).

  Definition tickBox : process _ _ := tickBoxLoop initState.
End trustedTickBox.
