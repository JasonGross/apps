(** * Skeleton of app that asks for GPS and a list of MBTA busses, and displays the ones near you *)
Require Import Coq.Strings.Ascii Coq.Program.Basics Coq.Strings.String.
Require Import Coq.Lists.List Coq.Sorting.Mergesort.
Require Import FunctionApp FunctionAppLemmas FunctionAppTactics.
Require Import TrustedTickBox Common.
Import ListNotations.

Local Open Scope program_scope.

Module Type GPSCoordinateType.
  Axiom t : Type.
  Axiom distance : t -> t -> nat.
  Axiom toString : t -> string.
  Axiom initGPS : t.
End GPSCoordinateType.

(** We implement the following diagram:

<<

                        receive bus list      System Clock (tick)
                              │                    │
                              V                    V
                      ┌────────────────────────────────────────────────────┐
                      │       │                    ├──────┐                │
                      │       V                    V      │                │
    update busses     │    ┌────┐ want busses   ┌──────┐  │                │
    --------------->  │ -> │    │ ------------> │ Bus  │  │ request busses │
                      │    │    │               │ Tick │ ----------------> │ --> internet
    update gps        │    │    │ <------------ │ Box  │  │                │
    --------------->  │ -> │    │ ------------> │      │  │                │
                      │    │    │               └──────┘  │                │
                      │    │ UI │                  ┌──────┘                │
    set max dist      │    │    │                  V                       │
    --------------->  │ -> │    │ want GPS      ┌──────┐                   │
                      │    │    │ ------------> │ GPS  │    request GPS    │
    console out       │    │    │               │ Tick │ ----------------> │--> GPS
    <---------------  │ <- │    │ <------------ │ Box  │                   │
                      │    └────┘ ------------> │      │                   │
                      │       ^                 └──────┘                   │
                      │       │                                            │
                      └────────────────────────────────────────────────────┘
                              ^
                              │
                        receive GPS
>>

    We will eventually want to add knobs for setting the parameters of
    the tick boxes.  The unlabeled double-way arrows are helpers for
    the tick boxes.  *)


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


      (** Separate out the body, so that the proof at the end compiles faster. *)
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
      | mbtaBadState
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
                | inl mbtaBadState =>
                  (stackPush mbtaBadState, mbtaLoop ui tbGPS tbBusses)
                | inl mbtaRequestGPS =>
                  let (a, tbGPS') := getStep tbGPS (inr (tbNotifyChange unit)) in
                  (a, mbtaLoop ui tbGPS' tbBusses)
                | inl mbtaRequestBusses =>
                  let (a, tbGPS') := getStep tbGPS (inr (tbNotifyChange unit)) in
                  (a, mbtaLoop ui tbGPS' tbBusses)
                | inl mbtaTbGPSRequestDataUpdate =>
                  (** We can just say that we're immediately ready with a value *)
                  let (a, tbGPS') := getStep tbGPS (inr (tbValueReady tt)) in
                  (a, mbtaLoop ui tbGPS' tbBusses)
                | inl mbtaTbBussesRequestDataUpdate =>
                  (** We can just say that we're immediately ready with a value *)
                  let (a, tbBusses') := getStep tbBusses (inr (tbValueReady tt)) in
                  (a, mbtaLoop ui tbGPS tbBusses')
                | inr (mbtaTick extraTicks) =>
                  let (a, tbGPS') := getStep tbGPS (inr (tbTick unit extraTicks)) in
                  let (a', tbBusses') := getStep tbBusses (inr (tbTick unit extraTicks)) in
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
        := (fun s : tbOutput unit
            => match s with
                 | inl (tbWarnInvalidEvent _ _) => stackPush mbtaBadState
                 | inr tbRequestDataUpdate => stackPush mbtaRequestGPS
                 | inr (tbPublishUpdate _) => stackLift (handle mbtaOutRequestGPSUpdate)
                 | inl _ => stackLift id
               end).

      Definition bussesHandler
        := (fun s : tbOutput unit
            => match s with
                 | inl (tbWarnInvalidEvent _ _) => stackPush mbtaBadState
                 | inr tbRequestDataUpdate => stackPush mbtaRequestBusses
                 | inr (tbPublishUpdate _) => stackLift (handle mbtaOutRequestBussesUpdate)
                 | inl _ => stackLift id
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
                                          (fun world handle => tickBox handle)
                                          (fun world handle => tickBox handle).

      CoFixpoint mbtaGood' uiSt gpsSt bussesSt
      : emptiesStackForever (Step (mbtaLoopBody mbtaLoop
                                                (uiLoop (stackWorld mbtaMessage world) uiHandler uiSt)
                                                (tickBoxLoop gpsHandler gpsSt)
                                                (tickBoxLoop bussesHandler bussesSt))).
      Proof.
        destruct gpsSt as [[]], bussesSt as [[]];
        constructor;
        let tac := (idtac;
                    match goal with
                      | [ |- appcontext[if ?E then _ else _] ]
                        => (let T := type of E in
                            constr_eq T bool;
                            case_eq E; intro)
                    end) in
        emptiesStackForever_t mbtaGood' mbtaInput (@mbtaLoop_eta) (@mbtaLoop) tac.
      Qed.

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
