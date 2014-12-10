(** * A box to prevent timing side channels (part of TCB) *)
Require Import Coq.Program.Basics Coq.NArith.NArith Coq.Lists.List.
Require Import FunctionApp TrustedTickBox.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope program_scope.

Section gateway.

  Context (world : Type).

  Inductive gatewayInput :=
  | GWakeUp
  | GClocksGot (nanoseconds : N).

  Definition nanos_per_tick := 1%N.
  Definition sleep_nanos := 1024%N.

  Open Scope N_scope.

  Inductive gatewayOutput :=
  | GOSleep (_ : N)
  | GOGetClock
  | GOTick (_ : N).

  Definition GatewayState := option N.

  Definition gatewayLoopPreBody (st : option N) : gatewayInput -> (list gatewayOutput) * GatewayState :=
    fun i =>
      match i with
        | GWakeUp =>
          (GOGetClock :: nil, st)
        | GClocksGot new =>
          let actions :=
              match st with
                | Some prev => 
                  let ticks := (new - prev) / nanos_per_tick in
                  GOTick ticks :: nil
                | None => nil
              end in
          (actions ++ GOSleep sleep_nanos :: nil, Some new)
      end.

  Context (handle : gatewayOutput -> action world).

  Definition gatewayLoopBody {T}
             (loop : GatewayState -> T)
             (st : GatewayState)
  : gatewayInput -> action world * T
    := fun i => let outputs := fst (gatewayLoopPreBody st i) in
                let st' := snd (gatewayLoopPreBody st i) in
                (fold_left compose (map handle outputs) id,
                 loop st').

  CoFixpoint gatewayLoop (st : option N) :=
    Step (gatewayLoopBody gatewayLoop st).

  Definition gatewayInitState : GatewayState := None.

  Definition gateway := gatewayLoop gatewayInitState.

End gateway.

Section tickBox.

  Variable dataT : Type.
  Context (world : Type).

  Inductive tbEventInput :=
  | tbNotifyChange
  | tbWakeUp
  | tbClocksGot (nanoseconds : N)
  | tbValueReady (val : dataT).

  Inductive tbEventOutput :=
  | tbRequestDataUpdate
  | tbPublishUpdate (val : dataT)
  | tbSleepNanosecs (nanos : N)
  | tbGetNanosecs.

  Definition tbInput := (tbConfigInput + tbEventInput)%type.
  Definition tbOutput := (tbWarningOutput dataT + tbEventOutput)%type.

  Definition to_tbOutput (a : TrustedTickBox.tbOutput dataT) :=
    match a with
      | inl x => inl x
      | inr (TrustedTickBox.tbRequestDataUpdate) => inr tbRequestDataUpdate
      | inr (TrustedTickBox.tbPublishUpdate x) => inr (tbPublishUpdate x)
    end.

  Notation TickBoxStateOrigin := (TrustedTickBox.TickBoxState dataT).

  Definition TickBoxState := (GatewayState * TickBoxStateOrigin)%type.

  Definition initState : TickBoxState := (gatewayInitState, TrustedTickBox.initState dataT).

  Definition tb := @TrustedTickBox.tickBoxLoopPreBody dataT.
  Definition gw := gatewayLoopPreBody.

  Definition convert := map to_tbOutput.

  Definition handle_gateway_output (o : gatewayOutput) (st : TickBoxStateOrigin) :=
    match o with
      | GOTick n => 
        let (o, st') := tb st (inr (tbTick dataT n)) in
        (convert o, st')
      | GOSleep n => (inr (tbSleepNanosecs n) :: nil, st)
      | GOGetClocks => (inr tbGetNanosecs :: nil, st)
    end.

  Definition handle_gateway_outputs outputs (st : TickBoxStateOrigin) :=
    fold_left 
      (fun (p : list _ * _) o => 
         let (acc, st) := p in 
         let (os, st') := handle_gateway_output o st in
         (acc ++ os, st')) 
      outputs (nil, st).

  Definition tickBoxLoopPreBody
             (st : TickBoxState)
  : tbInput -> (list tbOutput) * TickBoxState :=
    fun i =>
      match i with
        | inl x =>
          let (a, b) := st in
          let (o, b') := tb b (inl x) in 
          (convert o, (a, b'))
        | inr tbNotifyChange =>
          let (a, b) := st in
          let (o, b') := tb b (inr (TrustedTickBox.tbNotifyChange dataT)) in 
          (convert o, (a, b'))
        | inr (tbValueReady x) =>
          let (a, b) := st in
          let (o, b') := tb b (inr (TrustedTickBox.tbValueReady x)) in 
          (convert o, (a, b'))
        | inr tbWakeUp =>
          let (a, b) := st in
          let (o, a') := gw a GWakeUp in
          let (o, b') := handle_gateway_outputs o b in
          (o, (a', b'))
        | inr (tbClocksGot x) =>
          let (a, b) := st in
          let (o, a') := gw a (GClocksGot x) in
          let (o, b') := handle_gateway_outputs o b in
          (o, (a', b'))
      end.

  Context (handle : tbOutput -> action world).

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

End tickBox.

