(** * A box to prevent timing side channels (part of TCB) *)
Require Import Coq.Program.Basics Coq.NArith.NArith Coq.Lists.List.
Require Import FunctionApp TrustedTickBox.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope program_scope.

Section gateway.

  Context (world : Type).
  Context (sleepNanosecs : N -> action world).
  Context (getNanosecs : action world).
  Context (tick : N -> action world).

  Inductive gatewayInput :=
  | GWakeUp
  | GClocksGot (nanoseconds : N).

  Definition nanos_per_tick := 1%N.
  Definition sleep_nanos := 1024%N.

  Open Scope N_scope.

  Definition gatewayLoopBody (loop : option N -> process gatewayInput world) (st : option N)
  : gatewayInput -> action world * process gatewayInput world
    := (fun i =>
          match i with
            | GWakeUp =>
              (getNanosecs, loop st)
            | GClocksGot new =>
              let action :=
                  match st with
                    | Some prev => 
                      let ticks := (new - prev) / nanos_per_tick in
                      compose (sleepNanosecs sleep_nanos) (tick ticks)
                    | None => id
                  end in
              (compose (sleepNanosecs sleep_nanos) action, loop (Some new))
          end).
                                       
  CoFixpoint gatewayLoop (st : option N) :=
    Step (gatewayLoopBody gatewayLoop st).

  Definition gateway := gatewayLoop None.

End gateway.

Section tickBox.

  Variable dataT : Type.
  Context (world : Type).

  Inductive tbConfigInput :=
  | tbSetPublishInterval (_ : N)
  | tbSetPublishDuration (_ : PublishDurationT)
  | tbSetWaitBeforeUpdateInterval (_ : N)
  | tbSetPublishPrecision (_ : N).

  Inductive tbEventInput :=
  | tbNotifyChange
  | tbWakeUp
  | tbClocksGot (nanoseconds : N)
  | tbValueReady (val : dataT).

  Definition tbInput := (tbConfigInput + tbEventInput)%type.

  Definition getStep {input output} (p : process input output) :=
    match p with
      | Step f => f
    end.

  Inductive tbMessage :=
  | tbTick (ticks : N).

  Definition tbLoopBody loop gateway tb : @stackInput tbMessage tbInput -> action (stackWorld tbMessage world) * stackProcess tbMessage tbInput world :=
    fun i =>
      match i with
        | inr (inl (tbSetPublishInterval x)) =>
          let (a, tb') := getStep tb (inl (TrustedTickBox.tbSetPublishInterval x)) in (a, loop gateway tb')
        | inr (inl (tbSetPublishDuration x)) =>
          let (a, tb') := getStep tb (inl (TrustedTickBox.tbSetPublishDuration x)) in (a, loop gateway tb')
        | inr (inl (tbSetWaitBeforeUpdateInterval x)) =>
          let (a, tb') := getStep tb (inl (TrustedTickBox.tbSetWaitBeforeUpdateInterval x)) in (a, loop gateway tb')
        | inr (inl (tbSetPublishPrecision x)) =>
          let (a, tb') := getStep tb (inl (TrustedTickBox.tbSetPublishPrecision x)) in (a, loop gateway tb')
        | inr (inr tbNotifyChange) =>
          let (a, tb') := getStep tb (inr (TrustedTickBox.tbNotifyChange dataT)) in (a, loop gateway tb')
        | inr (inr (tbValueReady x)) =>
          let (a, tb') := getStep tb (inr (TrustedTickBox.tbValueReady x)) in (a, loop gateway tb')
        | inr (inr tbWakeUp) =>
          let (a, gateway') := getStep gateway GWakeUp in (a, loop gateway' tb)
        | inr (inr (tbClocksGot x)) =>
          let (a, gateway') := getStep gateway (GClocksGot x) in (a, loop gateway' tb)
        | inl (tbTick x) =>
          let (a, tb') := getStep tb (inr (TrustedTickBox.tbTick dataT x)) in (a, loop gateway tb')
      end.

  CoFixpoint tbLoop gateway tb : stackProcess tbMessage tbInput world :=
    Step (tbLoopBody tbLoop gateway tb).

  Require Import System.

  Context (sys : systemActions tbInput world).
  Definition sleepNanosecs (nanos : N) := System.sleepNanosecs sys nanos (inr tbWakeUp).
  Definition getNanosecs := System.getNanosecs sys (compose inr tbClocksGot).

  Definition
    wrap_gateway
    (gateway :
       forall {world'},
         (N -> action world') ->
         (action world') ->
         (N -> action world') ->
         process gatewayInput world') :=
    gateway
      (fun s => stackLift (sleepNanosecs s))
      (stackLift getNanosecs)
      (fun s => stackPush (tbTick s)).

  Notation tbOutputOrigin := (TrustedTickBox.tbOutput dataT).
  Notation tbInputOrigin := (TrustedTickBox.tbInput dataT).

  Context (handle : tbOutputOrigin -> action world).

  Definition
    wrap_tb
    (tb :
       forall {world'},
         (tbOutputOrigin -> action world') ->
         process tbInputOrigin world') :=
    tb
      (fun s => @stackLift tbMessage world (handle s)).

  Definition
    mkTickBoxStack gateway tb :
    stackProcess tbMessage tbInput world :=
    tbLoop (wrap_gateway gateway) (wrap_tb tb).

  Definition tbStack := mkTickBoxStack gateway (@TrustedTickBox.tickBox dataT).

  Theorem tbGood : emptiesStackForever tbStack.
  Proof.
    admit.
  Qed.

  Definition tickBox := runStackProcess tbStack tbGood.

End tickBox.

