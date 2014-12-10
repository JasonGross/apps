(** * A box to prevent timing side channels (part of TCB) *)
Require Import Coq.Program.Basics Coq.NArith.NArith Coq.Lists.List.
Require Import FunctionApp TrustedTickBox.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope program_scope.

Section tickG.

  Context (world : Type).

  Inductive tickGInput :=
  | TGWakeUp
  | TGClocksGot (nanoseconds : N).

  Definition nanos_per_tick := 1%N.
  Definition sleep_nanos := 1024%N.

  Open Scope N_scope.

  Inductive tickGOutput :=
  | TGSleepNanosecs (_ : N)
  | TGGetNanosecs
  | TGTick (_ : N).

  Definition GatewayState := option N.

  Definition tickGLoopPreBody (st : option N) : tickGInput -> (list tickGOutput) * GatewayState :=
    fun i =>
      match i with
        | TGWakeUp =>
          (TGGetNanosecs :: nil, st)
        | TGClocksGot new =>
          let actions :=
              match st with
                | Some prev => 
                  let ticks := (new - prev) / nanos_per_tick in
                  TGTick ticks :: nil
                | None => nil
              end in
          (TGSleepNanosecs sleep_nanos :: actions, Some new)
      end.

  Context (handle : tickGOutput -> action world).

  Definition tickGLoopBody {T}
             (loop : GatewayState -> T)
             (st : GatewayState)
  : tickGInput -> action world * T
    := fun i => let outputs := fst (tickGLoopPreBody st i) in
                let st' := snd (tickGLoopPreBody st i) in
                (fold_left compose (map handle outputs) id,
                 loop st').

  CoFixpoint tickGLoop (st : option N) :=
    Step (tickGLoopBody tickGLoop st).

  Definition tickGInitState : GatewayState := None.

  Definition tickG := tickGLoop tickGInitState.

End tickG.