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
    ---------------→  │          │
                      │          │
    publish value     │          │
      (data in)       │ Tick Box │ -----→ publish update (data out)
    ---------------→  │          │
                      │          │
    ←---------------  │          │
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
    Box will publish its current value, and then request an updated
    value from the encryption box.  The encryption box should
    construct a unique encryption (using its own source of
    randomness), and raise the "publish value (data in)" event with
    that new value.

    The tick box will emit a warning if it has not recieved a "publish
    value (data in)" event after its most recent request when it is
    time to publish an update.  In this case, we will defer publishing
    an update of our value, leaking timing information.  (Leaking
    information through timing is unavoidable in this case.)

    The tick box will emit a separate warning if it detects that the
    program is being insufficiently responsive, and that the number of
    ticks between publishes is different from [X] by at least [Z].

    ** Configurable parameters

    - [publishInterval] ([X] above) - the number of ticks to wait
      between successive publishings.  A value of [0] means to publish
      as soon as the number of ticks increments.

    - [publishDuration] ([Y] above) - the number of [PublishInterval]s
      after the most recent change to continue publishing updates.  A
      value of [0] means to publish at most once for each change.  A
      special flag value of [∞] means to always publish.

    - [publishPrecision] ([Z] above) - Suppose the clock does not
      publish on every tick, and we find that, previously, we were
      given tick [X₀ < X], and on the current update, we are given [X₁
      > X].  We will emit a warning iff [X₁ - X > Z + 1].


    Note: Setting [PublishInterval] is a privlidged operation: if it
          is set too low, then there will not be time to complete the
          computation between successive publishes, and timing
          information will be leaked.

          Similarly, if [PublishDuration] is set to any value other
          than [∞], a controlled amount of timing information is
          leaked.

    TODO: Do we want to publish in multiples of [X] according to the
          system clock, or do we want to publish [X] ticks after
          whenever the last time we managed to publish was?
          Currently, we do the latter.

    TODO: Implement the optimization where we ask to shut off tick
          notifications if we haven't seen updates recently. *)

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

Section trustedTickBox.
  Variable dataT : Type.

  Record TickBoxState :=
    {
      curData :> dataT;
      ticksSinceLastPublish : nat;
      publishesSinceLastChange : nat;
      changeSinceLastPublish : bool;
      updateReceivedSincePublish : bool;
      publishInterval : nat;
      publishDuration : PublishDurationT;
      publishPrecision : nat
    }.

(* python:
<<
fields=[(x.strip(), y.strip()) for x, y in [z.split(':') for z in """
      curData : dataT;
      ticksSinceLastPublish : nat;
      publishesSinceLastChange : nat;
      changeSinceLastPublish : bool;
      updateReceivedSincePublish : bool;
      publishInterval : nat;
      publishDuration : PublishDurationT;
      publishPrecision : nat""".split(';')]]
for field0, ty0 in fields:
    body = ';\n          '.join((('%s := st.(%s)' % (field, field)) if field != field0 else ('%s := v' % field))
                                for field, ty in fields)
    print('  Definition set_%s (st : TickBoxState) (v : %s)' % (field0, ty0))
    print('    := {| ' + body + ' |}.\n')
>> *)

  Definition set_curData (st : TickBoxState) (v : dataT)
    := {| curData := v;
          ticksSinceLastPublish := st.(ticksSinceLastPublish);
          publishesSinceLastChange := st.(publishesSinceLastChange);
          changeSinceLastPublish := st.(changeSinceLastPublish);
          updateReceivedSincePublish := st.(updateReceivedSincePublish);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_ticksSinceLastPublish (st : TickBoxState) (v : nat)
    := {| curData := st.(curData);
          ticksSinceLastPublish := v;
          publishesSinceLastChange := st.(publishesSinceLastChange);
          changeSinceLastPublish := st.(changeSinceLastPublish);
          updateReceivedSincePublish := st.(updateReceivedSincePublish);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_publishesSinceLastChange (st : TickBoxState) (v : nat)
    := {| curData := st.(curData);
          ticksSinceLastPublish := st.(ticksSinceLastPublish);
          publishesSinceLastChange := v;
          changeSinceLastPublish := st.(changeSinceLastPublish);
          updateReceivedSincePublish := st.(updateReceivedSincePublish);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_changeSinceLastPublish (st : TickBoxState) (v : bool)
    := {| curData := st.(curData);
          ticksSinceLastPublish := st.(ticksSinceLastPublish);
          publishesSinceLastChange := st.(publishesSinceLastChange);
          changeSinceLastPublish := v;
          updateReceivedSincePublish := st.(updateReceivedSincePublish);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_updateReceivedSincePublish (st : TickBoxState) (v : bool)
    := {| curData := st.(curData);
          ticksSinceLastPublish := st.(ticksSinceLastPublish);
          publishesSinceLastChange := st.(publishesSinceLastChange);
          changeSinceLastPublish := st.(changeSinceLastPublish);
          updateReceivedSincePublish := v;
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_publishInterval (st : TickBoxState) (v : nat)
    := {| curData := st.(curData);
          ticksSinceLastPublish := st.(ticksSinceLastPublish);
          publishesSinceLastChange := st.(publishesSinceLastChange);
          changeSinceLastPublish := st.(changeSinceLastPublish);
          updateReceivedSincePublish := st.(updateReceivedSincePublish);
          publishInterval := v;
          publishDuration := st.(publishDuration);
          publishPrecision := st.(publishPrecision) |}.

  Definition set_publishDuration (st : TickBoxState) (v : PublishDurationT)
    := {| curData := st.(curData);
          ticksSinceLastPublish := st.(ticksSinceLastPublish);
          publishesSinceLastChange := st.(publishesSinceLastChange);
          changeSinceLastPublish := st.(changeSinceLastPublish);
          updateReceivedSincePublish := st.(updateReceivedSincePublish);
          publishInterval := st.(publishInterval);
          publishDuration := v;
          publishPrecision := st.(publishPrecision) |}.

  Definition set_publishPrecision (st : TickBoxState) (v : nat)
    := {| curData := st.(curData);
          ticksSinceLastPublish := st.(ticksSinceLastPublish);
          publishesSinceLastChange := st.(publishesSinceLastChange);
          changeSinceLastPublish := st.(changeSinceLastPublish);
          updateReceivedSincePublish := st.(updateReceivedSincePublish);
          publishInterval := st.(publishInterval);
          publishDuration := st.(publishDuration);
          publishPrecision := v |}.

  Inductive tbInput :=
  | tbNotifyChange
  | tbTick (addedTickCount : nat)
  | tbValueReady (val : dataT)
  | tbSetPublishInterval (_ : nat)
  | tbSetPublishDuration (_ : PublishDurationT)
  | tbSetPublishPrecision (_ : nat).

  Inductive tbOutput :=
  | tbRequestDataUpdate
  | tbPublishUpdate (val : dataT)
  | tbWarnNoDataReady
  | tbWarnTicksTooInfrequent.


  Context (world : Type)
          (initData : dataT)
          (handle : tbOutput -> action world).

  Definition initState : TickBoxState :=
    {| curData := initData;
       ticksSinceLastPublish := 0;
       publishesSinceLastChange := 0;
       changeSinceLastPublish := false;
       updateReceivedSincePublish := true;
       publishInterval := 0;
       publishDuration := ∞;
       publishPrecision := 0 |}.

  (** Does the security policy mandate that we should publish the
      state? *)
  Definition shouldPublish (st : TickBoxState) : bool :=
    ((st.(ticksSinceLastPublish) >? st.(publishInterval))
       && ((st.(changeSinceLastPublish))
             || (st.(publishesSinceLastChange) <=? st.(publishDuration)))).

  (** Do we have data that we're ready to publish? *)
  Definition canPublish (st : TickBoxState) : bool :=
    st.(updateReceivedSincePublish).

  (** Should we reset the tick counter, claiming that we've finished?
      Yes, if we could be publishing, and we've seen enough ticks to
      allow us to publish; we don't want to spew warnings when we've
      seen enough ticks to publish, but we've already published enough
      new data. *)
  Definition shouldResetTicks (st : TickBoxState) : bool :=
    canPublish st && (st.(ticksSinceLastPublish) >? st.(publishInterval)).

  (** Should we emit a warning about [tbTick] not being called often
      enough? *)
  Definition shouldWarnInfrequentTicks (st : TickBoxState) : bool :=
    st.(ticksSinceLastPublish) - st.(publishInterval) >? st.(publishPrecision) + 1.

  (** Should we emit a warning that we're supposed to publish data
      more frequently than we're getting updates? *)
  Definition shouldWarnNoDataReady (st : TickBoxState) : bool :=
    shouldPublish st && negb (canPublish st).

  (** Reset the ticks *)
  Definition resetTicks (st : TickBoxState) : TickBoxState :=
    {| curData := st.(curData);
       ticksSinceLastPublish := 0;
       publishesSinceLastChange := if st.(changeSinceLastPublish)
                                   (** if there's been a change since we last computed [curData], we want to reset the counter. *)
                                   then 0
                                   else (st.(publishesSinceLastChange) + 1);
       changeSinceLastPublish := false;
       updateReceivedSincePublish := false;
       publishInterval := st.(publishInterval);
       publishDuration := st.(publishDuration);
       publishPrecision := st.(publishPrecision) |}.

  Definition tickBoxLoopBody
             (tickBoxLoop : TickBoxState -> process tbInput world)
             (st : TickBoxState)
  : tbInput -> action world * process tbInput world
    := fun i =>
         match i with

           | tbSetPublishInterval val
             => (id, tickBoxLoop (set_publishInterval st val))

           | tbSetPublishDuration val
             => (id, tickBoxLoop (set_publishDuration st val))

           | tbSetPublishPrecision val
             => (id, tickBoxLoop (set_publishPrecision st val))

           | tbNotifyChange
             => (id, tickBoxLoop (set_changeSinceLastPublish st true))

           | tbValueReady val
             => (id, tickBoxLoop (set_curData st val))

           | tbTick ticksSinceLastTick
             => let tickCount := st.(ticksSinceLastPublish) + ticksSinceLastTick in
                let st' := set_ticksSinceLastPublish st tickCount in
                let actions := id in
                let actions := (if shouldWarnInfrequentTicks st'
                                then actions ∘ handle tbWarnTicksTooInfrequent
                                else actions) in
                let actions := (if shouldWarnNoDataReady st'
                                then actions ∘ handle tbWarnNoDataReady
                                else actions) in
                let tb' := tickBoxLoop (if shouldResetTicks st'
                                        then resetTicks st'
                                        else st') in
                ((if canPublish st' && shouldPublish st'

                  then (** XXX TODO FIXME: we must have that the
                             publish comes first, or else this box is
                             useless.  Does [foo ∘ bar] mean "first
                             [bar], then [foo]" or "first [foo], then
                             [bar]"? *)
                    actions ∘ handle tbRequestDataUpdate ∘ handle (tbPublishUpdate st'.(curData))
                  else actions),
                 tb')

         end.

  CoFixpoint tickBoxLoop (st : TickBoxState) :=
    Step (tickBoxLoopBody tickBoxLoop st).

  Definition tickBox : process _ _ := tickBoxLoop initState.
End trustedTickBox.
