Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Program.Basics Coq.Program.Program Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Coq.NArith.BinNat.
Require Import SerializableMergableFMapInterface StringKey PrefixSerializable.
Require Import System FunctionApp FunctionAppLemmas FunctionAppTactics.
Require Import PwMgrUI PwMgrWarningBox TrustedServerSyncBox EncryptionInterface.
Import ListNotations.
Open Scope string_scope.


Section net.

  Inductive netInput :=
| netReceived : option string -> netInput
| netHttpError : httpResponse -> netInput
| netEncrypted : string -> netInput.

  Context (world : Type).
  Context (httpPOST : string -> list (string * string) -> (httpResponse -> netInput) -> action world).
  Context (decrypt : string -> action world).

  Definition storageURI := "https://andersk.scripts.mit.edu/pwmgr/storage".
  Definition storageId := "foo".

  Definition storageGet id cb :=
    httpPOST
      (storageURI ++ "/get") [("id", id)]
      (fun r => match httpResponseStatus r with
                  | httpOk => cb (httpResponseBody r)
                  | _ => netHttpError r
                end).
  Definition storageSet id old new cb :=
    httpPOST
      (storageURI ++ "/set") [("id", id); ("old", old); ("new", new)]
      (fun r => match httpResponseStatus r with
                  | httpOk => cb None  (* compare-and-set succeeded *)
                  | httpPreconditionFailed => cb (Some (httpResponseBody r))  (* remote value differed *)
                  | _ => netHttpError r
                end).
  Definition storagePoll id old cb :=
    httpPOST
      (storageURI ++ "/poll") [("id", id); ("old", old)]
      (fun r => match httpResponseStatus r with
                  | httpOk => cb (httpResponseBody r)
                  | _ => netHttpError r
                end).

  CoFixpoint net :=
    Step (fun i =>
            match i with
              | netReceived (Some s) => (decrypt s, net)
              | netReceived None => (id, net)
              | netHttpError _ => (id, net)
              | netEncrypted s =>
                (storageSet storageId "" s netReceived,
                 net)
            end).

End net.

Definition getStep {input output} (p : process input output) :=
  match p with
    | Step f => f
  end.

Local Open Scope type_scope.

Module MakePwMgr
       (KVStore : SerializableMergableMapInterface String_as_SOT)
       (Algorithm : EncryptionAlgorithm EncryptionStringDataTypes).
  Module SSB := TrustedServerSyncBox EncryptionStringDataTypes Algorithm.
  Module WB := PwMgrWarningBox Algorithm.
  Module UI := PwMgrUI KVStore.

  (** Coq is stupid and doesn't recognize equality of identical module instantiations. *)
  Coercion eta_ebError (a : SSB.TEB.ebErrorOutput) : WB.SSB.TEB.ebErrorOutput
    := match a with
         | SSB.TEB.ebErrorNotEnoughRandomness howMuchWanted randomnessGiven
           => WB.SSB.TEB.ebErrorNotEnoughRandomness howMuchWanted randomnessGiven
         | SSB.TEB.ebErrorInvalidMasterKey key pf
           => WB.SSB.TEB.ebErrorInvalidMasterKey (key := key) pf
         | SSB.TEB.ebErrorNoMasterKey
           => WB.SSB.TEB.ebErrorNoMasterKey
       end.

  Coercion eta_dbError {T} (a : SSB.TDB.dbErrorOutput T) : WB.SSB.TDB.dbErrorOutput T
    := match a with
         | SSB.TDB.dbErrorInvalidData data tag
           => WB.SSB.TDB.dbErrorInvalidData data tag
         | SSB.TDB.dbErrorInvalidMasterKey key pf
           => WB.SSB.TDB.dbErrorInvalidMasterKey T (key := key) pf
         | SSB.TDB.dbErrorNoMasterKey
           => WB.SSB.TDB.dbErrorNoMasterKey T
       end.

  Coercion eta_ssbConfigInput (a : SSB.ssbConfigInput) : WB.SSB.ssbConfigInput
    := match a with
         | SSB.ssbGetUpdateConfig b => WB.SSB.ssbGetUpdateConfig b
         | SSB.ssbCASConfig b       => WB.SSB.ssbCASConfig b
         | SSB.ssbSetMasterKey key  => WB.SSB.ssbSetMasterKey key
       end.

  Coercion eta_ssbEventInput (a : SSB.ssbEventInput) : WB.SSB.ssbEventInput
    := match a with
         | SSB.ssbTick addedTickCount             => WB.SSB.ssbTick addedTickCount
         | SSB.ssbClientGetUpdate                 => WB.SSB.ssbClientGetUpdate
         | SSB.ssbClientSet newD                  => WB.SSB.ssbClientSet newD
         | SSB.ssbServerGotUpdate newE            => WB.SSB.ssbServerGotUpdate newE
         | SSB.ssbSystemRandomness randomness tag => WB.SSB.ssbSystemRandomness randomness tag
       end.

  Coercion eta_ssbInput (a : SSB.ssbInput) : WB.SSB.ssbInput
    := match a with
         | inl x => inl (x : WB.SSB.ssbConfigInput)
         | inr x => inr (x : WB.SSB.ssbEventInput)
       end.

  Coercion eta_EncryptBoxState (a : SSB.TEB.EncryptBoxState) : WB.SSB.TEB.EncryptBoxState
    := {| WB.SSB.TEB.masterKey := a.(SSB.TEB.masterKey) |}.

  Coercion eta_DecryptBoxState (a : SSB.TDB.DecryptBoxState) : WB.SSB.TDB.DecryptBoxState
    := {| WB.SSB.TDB.masterKey := a.(SSB.TDB.masterKey) |}.

  Coercion eta_ServerSyncBoxPreState (a : SSB.ServerSyncBoxPreState) : WB.SSB.ServerSyncBoxPreState
    := {| WB.SSB.localStateD := a.(SSB.localStateD);
          WB.SSB.remoteStateE := a.(SSB.remoteStateE) |}.

  Coercion eta_ServerSyncBoxState (a : SSB.ServerSyncBoxState) : WB.SSB.ServerSyncBoxState
    := {| WB.SSB.ssbState          := a.(SSB.ssbState);
          WB.SSB.ssbGetUpdateState := a.(SSB.ssbGetUpdateState);
          WB.SSB.ssbCASState       := a.(SSB.ssbCASState);
          WB.SSB.ssbEncryptState   := a.(SSB.ssbEncryptState);
          WB.SSB.ssbDecryptState   := a.(SSB.ssbDecryptState) |}.

  Coercion eta_ssbWarning (a : SSB.ssbWarningOutput) : WB.SSB.ssbWarningOutput
    := match a with
         | SSB.ssbGetUpdateWarning b             => WB.SSB.ssbGetUpdateWarning b
         | SSB.ssbCASWarning b                   => WB.SSB.ssbCASWarning b
         | SSB.ssbEncryptError b                 => WB.SSB.ssbEncryptError b
         | SSB.ssbDecryptError b                 => WB.SSB.ssbDecryptError b
         | SSB.ssbWarningInvalidTransition ev st => WB.SSB.ssbWarningInvalidTransition ev st
         | SSB.ssbWarningPushBeforePull          => WB.SSB.ssbWarningPushBeforePull
       end.

  Section pwMgr.

    Inductive pwInput :=
    | pwMgrConsoleIn (line : string)
    | pwMgrNetInput (response : netInput)
    | pwMgrGotRandomness (key : EncryptionStringDataTypes.rawDataT) (randomness : string).

    Context (world : Type).
    Context (sys : systemActions pwInput world).

    Inductive pwMgrMessage :=
    | pwUI (msg : UI.uiOutput)
    | pwW (msg : WB.wOutput)
    | pwSSB (msg : SSB.ssbOutput)
    | pwBadState.
Axiom admit : forall {T}, T.
    Definition pwMgrLoopBody pwMgrLoop ssb wb ui net
    : @stackInput pwMgrMessage pwInput -> action (stackWorld pwMgrMessage world) * stackProcess pwMgrMessage pwInput world :=
      fun i =>
        match i with
          | inr (pwMgrConsoleIn s) =>
            let (a, ui') := getStep ui (UI.uiConsoleIn s) in
            (a ∘ stackLift (sys.(consoleIn) pwMgrConsoleIn), pwMgrLoop ssb wb ui' net)
          | inr (pwMgrNetInput i') =>
            let (a, net') := getStep net i' in
            (a, pwMgrLoop ssb wb ui net')
          | inr (pwMgrGotRandomness key randomness) =>
            let (a, ssb') := getStep ssb (inr (SSB.ssbSystemRandomness randomness key) : SSB.ssbInput) in
            (a, pwMgrLoop ssb' wb ui net)

          (* loop on bad states, spewing warnings (TODO: to stderr); I
             don't know which order messages are used in, so emit both
             before and after the [stackPush] *)
          | inl pwBadState
            => ((stackLift (sys.(consoleOut) "BAD LOOP"))
                  ∘ (stackPush pwBadState)
                  ∘ (stackLift (sys.(consoleOut) "BAD LOOP")),
                pwMgrLoop ssb wb ui net)

          | inl (pwUI UI.uiGetUpdate)
            => let (a, ssb') := getStep ssb (inr SSB.ssbClientGetUpdate : SSB.ssbInput) in
               (a, pwMgrLoop ssb' wb ui net)
          | inl (pwUI (UI.uiSetData data))
            => let (a, ssb') := getStep ssb (inr (SSB.ssbClientSet data) : SSB.ssbInput) in
               (a, pwMgrLoop ssb' wb ui net)
          | inl (pwUI (UI.uiConsoleOut data))
            => (stackLift (sys.(consoleOut) data), pwMgrLoop ssb wb ui net)

          | inl (pwW (WB.wConsoleErr lines))
            (* TODO: to stderr *)
            => (stackLift (sys.(consoleOut) lines), pwMgrLoop ssb wb ui net)

          | inl (pwW (WB.wBad msg))            (* TODO: to stderr *)
            => ((stackLift (sys.(consoleOut) msg))
                  ∘ (stackPush pwBadState)
                  ∘ (stackLift (sys.(consoleOut) msg)),
                pwMgrLoop ssb wb ui net)

          | inl (pwSSB (inl warning))
            => let (a, wb') := getStep wb (warning : WB.wInput) in
               (a, pwMgrLoop ssb wb' ui net)
          | inl (pwSSB (inr (SSB.ssbClientGotUpdate data)))
            => let (a, ui') := getStep ui (UI.uiGotUpdate data) in
               (a, pwMgrLoop ssb wb ui' net)
          | inl (pwSSB (inr (SSB.ssbRequestSystemRandomness howMuch tag)))
            => (stackLift (sys.(getRandomness) (N.of_nat howMuch) (pwMgrGotRandomness tag)),
                pwMgrLoop ssb wb ui net)


          | inl (pwSSB (inr SSB.ssbServerGetUpdate)) => admit
          | inl (pwSSB (inr (SSB.ssbServerCAS cur new))) => admit
        end.

    CoFixpoint pwMgrLoop ssb wb ui net : stackProcess pwMgrMessage pwInput world :=
      Step (pwMgrLoopBody pwMgrLoop ssb wb ui net).

    Definition
      wrap_ui
      (ui :
         forall {world'},
           (UI.uiOutput -> action world') ->
           process UI.uiInput world') :=
      ui
        (stackPush (world := world) ∘ pwUI).

    Definition
      wrap_ssb
      (ssb :
         forall {world'},
           (SSB.ssbOutput -> action world') ->
           process SSB.ssbInput world') :=
      ssb
        (stackPush (world := world) ∘ pwSSB).

    Definition
      wrap_wb
      (wb :
         forall {world'},
           (WB.wOutput -> action world') ->
           process WB.wInput world') :=
      wb
        (stackPush (world := world) ∘ pwW).

    Definition
      wrap_net
      (net :
         forall {world'},
           (string -> list (string * string) -> (httpResponse -> netInput) -> action world') ->
           (string -> action world') ->
           process netInput world') :=
      net
        (fun uri data cb => stackLift (httpPOST sys uri data (fun r => pwMgrNetInput (cb r))))
        (fun s => stackPush (pwMgrDecrypt s)).

    Definition
      mkPwMgrStack ui net :
      stackProcess pwMgrMessage input world :=
      pwMgrLoop (wrap_ui ui) (wrap_net net).

    Definition pwMgrStack := mkPwMgrStack ui net.


    Lemma pwMgrLoop_eta ui net
    : pwMgrLoop ui net = Step (pwMgrLoopBody pwMgrLoop ui net).
    Proof.
      rewrite stackProcess_eta at 1; reflexivity.
    Qed.

    (*
  CoFixpoint pwMgrGood' :
    forall pws, emptiesStackForever
      (Step (pwMgrLoopBody pwMgrLoop (wrap_ui (fun world uiConsoleOut uiEncrypt => uiLoop world uiConsoleOut uiEncrypt pws)) (wrap_net net))).
  Proof.
    intro; constructor.
    let tac := (idtac;
                match goal with
                  | [ |- appcontext[match split ?a ?b with _ => _ end] ] => destruct (split a b)
                  | [ |- appcontext[match string_dec ?s0 ?s1 with _ => _ end] ] => destruct (string_dec s0 s1)
                  | [ |- appcontext[match ?l with nil => _ | _ => _ end] ] => destruct l
                  | [ |- appcontext[match find ?f ?ls with _ => _ end] ] => destruct (find f ls)
                  | [ |- appcontext[match ?x with (_, _) => _ end] ] => rewrite (@surjective_pairing _ _ x)
                end) in
    emptiesStackForever_t pwMgrGood' input (@pwMgrLoop_eta) (@pwMgrLoop) tac.
  Qed.
     *)

    Theorem pwMgrGood pws :
      emptiesStackForever
        (mkPwMgrStack
           (fun world uiConsoleOut uiEncrypt => uiLoop world uiConsoleOut uiEncrypt pws)
           net).
    Proof.
      unfold mkPwMgrStack.
      rewrite pwMgrLoop_eta.
      (*
    eapply pwMgrGood'.
       *)
      admit.
    Qed.

    Definition proc := (consoleIn sys pwMgrConsoleIn, runStackProcess pwMgrStack (pwMgrGood nil)).

  End pwMgr.


  Require Import ExtrOcamlBasic ExtrOcamlString.
Extraction "ExamplePwMgr" proc.
