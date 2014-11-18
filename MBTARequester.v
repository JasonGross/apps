Require Import Coq.Strings.Ascii Coq.Program.Basics Coq.Strings.String.
Require Import Coq.Lists.List Coq.Sorting.Mergesort.
Require Import FunctionApp FunctionAppLemmas.
Require Import TrustedTickBox Common.
Import ListNotations.

Local Open Scope program_scope.

Module Type GPSCoordinateType.
  Axiom t : Type.
  Axiom distance : t -> t -> nat.
  Axiom toString : t -> string.
  Axiom initGPS : t.
End GPSCoordinateType.

Module MBTARequester (GPS : GPSCoordinateType).
  Local Notation GPSCoordinate := GPS.t.

  Module TotalLeBool'StringGPS <: Orders.TotalLeBool'.
    Definition t := (string * GPS.t * nat)%type.
    Definition leb (x y : t) := NatOrder.leb (snd x) (snd y).
    Definition leb_total (x y : t) : leb x y = true \/ leb y x = true
      := NatOrder.leb_total _ _.
  End TotalLeBool'StringGPS.

  Module SortGPSString := Sort TotalLeBool'StringGPS.
  Local Notation sort := SortGPSString.sort.

  Section components.
    Section ui.
      Inductive uiInput :=
      | uiRequestUpdate : uiInput
      | uiSetMaxDist : nat -> uiInput
      | uiGotGPS : GPSCoordinate -> uiInput
      | uiGotBusses : list (string * GPSCoordinate) -> uiInput.

      Inductive uiOutput :=
      | uiOutRequestGPSUpdate
      | uiOutRequestBusUpdate
      | uiConsoleOut (text : string).

      Context (world : Type)
              (handle : uiOutput -> action world).

      Definition newline := "010"%char.

      Definition dump (busList : list (string * GPSCoordinate)) : string
        := fold_right append ""%string
                      (map (fun p => (fst p ++ ": " ++ GPS.toString (snd p) ++ String newline ""))
                           busList)%string.

      Record state :=
        {
          curGPS : GPSCoordinate;
          curBusList : list (string * GPSCoordinate);
          curMaxDist : nat
        }.

      Definition initState : state :=
        {| curGPS := GPS.initGPS;
           curBusList := [];
           curMaxDist := 0 |}.

      Definition setGPS (st : state) (newGPS : GPSCoordinate) : state
        := {| curGPS := newGPS;
              curBusList := st.(curBusList);
              curMaxDist := st.(curMaxDist) |}.

      Definition setBusList (st : state) newBusList : state
        := {| curGPS := st.(curGPS);
              curBusList := newBusList;
              curMaxDist := st.(curMaxDist) |}.

      Definition setMaxDist (st : state) newMaxDist : state
        := {| curGPS := st.(curGPS);
              curBusList := st.(curBusList);
              curMaxDist := newMaxDist |}.

      Definition getInterestingBusses (st : state) : list (string * GPSCoordinate)
        := map
             (@fst _ _)
             (sort (filter
                      (fun scd => let dist := snd scd in
                                  NatOrder.leb dist st.(curMaxDist))
                      (map
                         (fun sc => let coord := snd sc in
                                    (sc, GPS.distance coord st.(curGPS)))
                         st.(curBusList)))).

      Definition dumpState : state -> string :=
        dump ∘ getInterestingBusses.



      Definition uiLoopBody
                 (uiLoop : state -> process uiInput world)
                 (st : state)
                 (sinput := uiInput)
                 (sworld := world)
      : sinput -> action sworld * process sinput sworld
        := fun i =>
             match i with

               | uiRequestUpdate
                 => (handle uiOutRequestGPSUpdate ∘ handle uiOutRequestBusUpdate, uiLoop st)

               | uiSetMaxDist newDist
                 => (id, uiLoop (setMaxDist st newDist))

               | uiGotGPS newGPS
                 => let st' := setGPS st newGPS in
                    (handle (uiConsoleOut (dumpState st')), uiLoop st')

               | uiGotBusses newBusList
                 => let st' := setBusList st newBusList in
                    (handle (uiConsoleOut (dumpState st')), uiLoop st')

             end.


      CoFixpoint uiLoop (st : state) :=
        Step (uiLoopBody uiLoop st).


      Definition ui : process _ _ := uiLoop initState.

    End ui.


    Definition getStep {input output} (p : process input output) :=
      match p with
        | Step f => f
      end.


    Section mbta.
      Inductive mbtaOutput :=
      | mbtaOutRequestGPSUpdate
      | mbtaOutRequestBussesUpdate
      | mbtaConsoleOut (text : string).

      Context (world : Type)
              (handle : mbtaOutput -> action world).

      Inductive mbtaMessage :=
      | mbtaRequestGPS
      | mbtaRequestBusses
      | mbtaTbGPSRequestDataUpdate
      | mbtaTbBussesRequestDataUpdate.

      Inductive mbtaInput :=
      | mbtaRequestUpdate : mbtaInput
      | mbtaSetMaxDist : nat -> mbtaInput
      | mbtaRecvGPS : GPSCoordinate -> mbtaInput
      | mbtaRecvBusses : list (string * GPSCoordinate) -> mbtaInput
      | mbtaTick (extraTicks : nat).

      Definition mbtaLoopBody
                 (mbtaLoop : forall
                               (ui : process uiInput (stackWorld mbtaMessage world))
                               (tbGPS
                                  tbBusses : process (tbInput unit)
                                                     (stackWorld mbtaMessage world)),
                               stackProcess mbtaMessage mbtaInput world)
                 (ui : process uiInput (stackWorld mbtaMessage world))
                 (tbGPS
                    tbBusses : process (tbInput unit)
                                       (stackWorld mbtaMessage world))
                 (sinput := (mbtaMessage + mbtaInput)%type)
                 (sworld := stackWorld mbtaMessage world)
      : sinput -> action sworld * process sinput sworld
        := (fun i =>
              match i with
                | inl mbtaRequestGPS =>
                  let (a, tbGPS') := getStep tbGPS (tbNotifyChange unit) in
                  (a, mbtaLoop ui tbGPS' tbBusses)
                | inl mbtaRequestBusses =>
                  let (a, tbGPS') := getStep tbGPS (tbNotifyChange unit) in
                  (a, mbtaLoop ui tbGPS' tbBusses)
                | inl mbtaTbGPSRequestDataUpdate =>
                  (** We can just say that we're immediately ready with a value *)
                  let (a, tbGPS') := getStep tbGPS (tbValueReady tt) in
                  (a, mbtaLoop ui tbGPS' tbBusses)
                | inl mbtaTbBussesRequestDataUpdate =>
                  (** We can just say that we're immediately ready with a value *)
                  let (a, tbBusses') := getStep tbBusses (tbValueReady tt) in
                  (a, mbtaLoop ui tbGPS tbBusses')
                | inr (mbtaTick extraTicks) =>
                  let (a, tbGPS') := getStep tbGPS (tbTick unit extraTicks) in
                  let (a', tbBusses') := getStep tbBusses (tbTick unit extraTicks) in
                  (a' ∘ a, mbtaLoop ui tbGPS' tbBusses')
                | inr mbtaRequestUpdate =>
                  let (a, ui') := getStep ui uiRequestUpdate in
                  (a, mbtaLoop ui' tbGPS tbBusses)
                | inr (mbtaSetMaxDist d) =>
                  let (a, ui') := getStep ui (uiSetMaxDist d) in
                  (a, mbtaLoop ui' tbGPS tbBusses)
                | inr (mbtaRecvGPS c) =>
                  let (a, ui') := getStep ui (uiGotGPS c) in
                  (a, mbtaLoop ui' tbGPS tbBusses)
                | inr (mbtaRecvBusses c) =>
                  let (a, ui') := getStep ui (uiGotBusses c) in
                  (a, mbtaLoop ui' tbGPS tbBusses)
              end).

      CoFixpoint mbtaLoop ui tbGPS tbBusses
      : stackProcess mbtaMessage mbtaInput world :=
        Step (mbtaLoopBody mbtaLoop ui tbGPS tbBusses).

      Lemma mbtaLoop_eta ui tbGPS tbBusses
      : mbtaLoop ui tbGPS tbBusses = Step (mbtaLoopBody mbtaLoop ui tbGPS tbBusses).
      Proof.
        rewrite stackProcess_eta at 1; reflexivity.
      Qed.

      Definition uiHandler
        := (fun s => match s with
                       | uiOutRequestGPSUpdate => stackPush mbtaRequestGPS
                       | uiOutRequestBusUpdate => stackPush mbtaRequestBusses
                       | uiConsoleOut text => stackLift (handle (mbtaConsoleOut text))
                     end).

      Definition gpsHandler
        := (fun s => match s with
                       | tbRequestDataUpdate => stackPush mbtaRequestGPS
                       | tbPublishUpdate tt => stackLift (handle mbtaOutRequestGPSUpdate)
                       | tbWarnNoDataReady => stackLift id
                       | tbWarnTicksTooInfrequent => stackLift id
                     end).

      Definition bussesHandler
        := (fun s => match s with
                       | tbRequestDataUpdate => stackPush mbtaRequestBusses
                       | tbPublishUpdate tt => stackLift (handle mbtaOutRequestBussesUpdate)
                       | tbWarnNoDataReady => stackLift id
                       | tbWarnTicksTooInfrequent => stackLift id
                     end).

      Definition mkMBTAStack
                 (ui :
                    forall {world'}
                           (handle : uiOutput -> action world'),
                      process uiInput world')
                 (tbGPS :
                    forall {world'}
                           (handle : tbOutput unit -> action world'),
                      process (tbInput unit) world')
                 (tbBusses :
                    forall {world'}
                           (handle : tbOutput unit -> action world'),
                      process (tbInput unit) world')
      : stackProcess mbtaMessage mbtaInput world :=
        mbtaLoop
          (ui uiHandler)
          (tbGPS gpsHandler)
          (tbBusses bussesHandler).

      Definition mbtaStack := mkMBTAStack ui
                                          (fun world handle => tickBox tt handle)
                                          (fun world handle => tickBox tt handle).

      Local Ltac emptiesStack_t loop_eta loop_pattern :=
        repeat match goal with
                 | [ |- emptiesStack (stackTransition _ _) _ ] => unfold stackTransition; simpl
                 | [ |- emptiesStack (stackPush _ _, _) _ ] => econstructor
                 | [ |- emptiesStack (stackLift _ _, _) _ ] => econstructor
                 | [ |- emptiesStack (stackDone, _) _ ] => constructor
                 | [ |- emptiesStack (_, ?p) _ ]
                   => let p' := head p in
                      constr_eq p' loop_pattern;
                        rewrite loop_eta; simpl
                 | [ |- emptiesStack (stackDone, ?p) ?q ] => apply emptiesStackDone'
                 | _ => progress unfold id
                 | _ => progress unfold compose
                 (*| [ |- ?p = ?e ?x ] => let T := type of x in is_evar e; unify e (fun _ : T => p); reflexivity*)
               end.

      Local Ltac prettify :=
        repeat match goal with
                 | [ |- appcontext[mbtaLoopBody _ (?uiLoop0 _) (?gpsLoop0 _) (?bussesLoop0 _)] ]
                   => progress (try change uiLoop0 with (@uiLoop _ uiHandler);
                                try change gpsLoop0 with (@tickBoxLoop unit _ gpsHandler);
                                try change bussesLoop0 with (@tickBoxLoop unit _ bussesHandler))
               end.

      Local Ltac t loopGood' inputT loop_eta loop_pattern :=
        repeat match goal with
                 | _ => progress simpl in *
                 | _ => intro
                 | [ |- _ /\ _ ] => split
                 | [ H : inputT |- _ ] => destruct H
                 | [ |- emptiesStack _ _ ] => clear loopGood'; emptiesStack_t loop_eta loop_pattern
                 | [ |- sig _ ] => eexists
                 | [ |- emptiesStackForever (Step _) ] => apply loopGood'
                 | [ |- emptiesStackForever ?p ]
                   => let p' := head p in
                      constr_eq p' loop_pattern;
                        rewrite loop_eta; simpl
               end.

      CoFixpoint mbtaGood' uiSt gpsSt bussesSt
      : emptiesStackForever (Step (mbtaLoopBody mbtaLoop
                                                (uiLoop (stackWorld mbtaMessage world) uiHandler uiSt)
                                                (tickBoxLoop gpsHandler gpsSt)
                                                (tickBoxLoop bussesHandler bussesSt))).
      Proof.
        apply emptiesStackStep'.
        t mbtaGood' mbtaInput mbtaLoop_eta (@mbtaLoop);
        prettify.
        repeat match goal with
                 | [ |- appcontext[if ?f ?x then _ else _] ]
                   => let H := fresh in
                      set (H := f x) in *
                 | [ |- appcontext[match ?E with tt => _ end] ] => destruct E
               end.
        (*Time repeat match goal with
                      | [ H : bool |- _ ] => destruct H
                    end;
          t mbtaGood' mbtaInput mbtaLoop_eta (@mbtaLoop).
        match goal with
                 (*| [ H := ?a && ?b |- _ ]
                   => let H1 := fresh in
                      let H2 := fresh in
                      set (H1 := a) in *;
                        set (H2 := b) in *;
                        subst H*)
                 | [ H1 := ?a, H2 := ?a |- _ ] => change H2 with H1 in *; clear H2
               end.
        repeat match goal with
                 | [ |- appcontext[if ?E then (fun x : ?T => @?a x) else (fun x : ?T => @?b x)] ]
                   => let t := constr:(if E then (fun x => a x) else (fun x => b x)) in
                      let t' := (eval cbv beta in t) in
                      progress replace t' with (fun x => if E then a x else b x) by (destruct E; reflexivity);
                        cbv beta
                 | [ |- appcontext[match ?E with tt => _ end] ] => destruct E

               end.
        match goal with
        Lemma if_assoc {T} (b1 b2 : bool) (a a' b : T)
        : (if b1 then (if b2 then a else a') else b) = if (b1 && b2) then a else if b1 then a' else b.
        Proof.
          destruct b1, b2; reflexivity.
        Defined.
        repeat rewrite !(pull_if (stackLift _)), !(pull_if (stackPush _)).
        rewrite !if_assoc.
        repeat rewrite !(pull_if (stackLift _)), !(pull_if (stackPush _)).
        progress repeat rewrite !(pull_if (stackLift _)), !(pull_if (stackPush _)).*)
      Admitted.

      Lemma mbtaGood
      : emptiesStackForever mbtaStack.
      Proof.
        rewrite stackProcess_eta.
        simpl; unfold tickBox, ui.
        apply mbtaGood'.
      Qed.

      Definition mbta := runStackProcess mbtaStack mbtaGood.

    End mbta.
  End components.

  Require Import ExtrOcamlBasic ExtrOcamlString.
  Extraction "ExampleMBTA" mbta.
End MBTARequester.
