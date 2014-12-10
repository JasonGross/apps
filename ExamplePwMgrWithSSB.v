Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Program.Basics Coq.Program.Program Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Coq.NArith.BinNat.
Require Import SerializableMergableFMapInterface StringKey PrefixSerializable.
Require Import System FunctionApp FunctionAppLemmas FunctionAppTactics.
Require Import PwMgrUI PwMgrWarningBox PwMgrNet TrustedServerSyncBox EncryptionInterface.
Import ListNotations.
Open Scope string_scope.

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

    Inductive input :=
    | pwMgrConsoleIn (line : string)
    | pwMgrNetInput (response : netInput)
    | pwMgrGotRandomness (key : EncryptionStringDataTypes.rawDataT) (randomness : string)
    | pwTick.

    Context (world : Type).
    Context (sys : systemActions input world).

    Inductive pwMgrMessage :=
    | pwUI (msg : UI.uiInput)
    | pwW (msg : WB.wInput)
    | pwSSB (msg : SSB.ssbInput)
    | pwNET (msg : netInput)
    | pwBadState.

    Definition one_second := 1000000000%N.

    Definition pwMgrLoopBody pwMgrLoop ssb wb ui net
    : @stackInput pwMgrMessage input -> action (stackWorld pwMgrMessage world) * stackProcess pwMgrMessage input world :=
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
          | inr pwTick =>
            (** TODO: Fix ticks *)
            let (a, ssb') := getStep ssb (inr (SSB.ssbTick 1) : SSB.ssbInput) in
            (stackLift (sys.(sleepNanosecs) one_second pwTick) ∘ a, pwMgrLoop ssb' wb ui net)

          (* loop on bad states, spewing warnings (TODO: to stderr) *)
          | inl pwBadState
            => (stackLift (sys.(consoleOut) "BAD LOOP" ∘ sys.(exit) 255),
                pwMgrLoop ssb wb ui net)

          | inl (pwNET ev) => let (a, net') := getStep net ev in (a, pwMgrLoop ssb wb ui net')
          | inl (pwUI ev)  => let (a, ui')  := getStep ui  ev in (a, pwMgrLoop ssb wb ui' net)
          | inl (pwW ev)   => let (a, wb')  := getStep wb  ev in (a, pwMgrLoop ssb wb' ui net)
          | inl (pwSSB ev) => let (a, ssb') := getStep ssb ev in (a, pwMgrLoop ssb' wb ui net)
        end.

    CoFixpoint pwMgrLoop ssb wb ui net : stackProcess pwMgrMessage input world :=
      Step (pwMgrLoopBody pwMgrLoop ssb wb ui net).

    Definition
      wrap_ui
      (ui :
         forall {world'},
           (UI.uiOutput -> action world') ->
           process UI.uiInput world') :=
      ui
        (fun i =>
           match i with
             | UI.uiGetUpdate
               => stackPush (pwSSB (inr SSB.ssbClientGetUpdate : SSB.ssbInput))
             | UI.uiSetData data
               => stackPush (pwSSB (inr (SSB.ssbClientSet data) : SSB.ssbInput))
             | UI.uiConsoleOut data
               => stackLift (sys.(consoleOut) data)
           end).

    Definition
      wrap_wb
      (wb :
         forall {world'},
           (WB.wOutput -> action world') ->
           process WB.wInput world') :=
      wb
        (fun i =>
           match i with
             | WB.wConsoleErr lines
               (* TODO: to stderr *)
               => stackLift (sys.(consoleOut) lines)
             | WB.wBad msg
               (* TODO: to stderr *)
               => (stackLift (sys.(consoleOut) msg))
                    ∘ (stackPush pwBadState)
           end).

    Definition
      wrap_ssb
      (ssb :
         forall {world'},
           (SSB.ssbOutput -> action world') ->
           process SSB.ssbInput world') :=
      ssb
        (fun i =>
           match i with
             | inl warning
               => stackPush (pwW (warning : WB.wInput))
             | inr (SSB.ssbClientGotUpdate data)
               => stackPush (pwUI (UI.uiGotUpdate data))
             | inr (SSB.ssbRequestSystemRandomness howMuch tag)
               => stackLift (sys.(getRandomness) (N.of_nat howMuch) (pwMgrGotRandomness tag))
             | inr SSB.ssbServerGetUpdate
               => stackPush (pwNET netGetUpdate)
             | inr (SSB.ssbServerCAS cur new)
               => stackPush (pwNET (netCAS cur new))
           end).

    Definition
      wrap_net
      (net :
         forall {world'},
           (netOutput -> action world') ->
           process netInput world') :=
      net (fun i =>
             match i with
               | netGotUpdate new
                 => stackPush (pwSSB (inr (SSB.ssbServerGotUpdate new)))
               | netHttpPOST uri data cb
                 => stackLift (httpPOST sys uri data (fun r => pwMgrNetInput (cb r)))
             end).

    Definition
      mkPwMgrStack ssb wb ui net :
      stackProcess pwMgrMessage input world :=
      pwMgrLoop (wrap_ssb ssb) (wrap_wb wb) (wrap_ui ui) (wrap_net net).

    Definition pwMgrStack (initStore : EncryptionStringDataTypes.rawDataT) (storageId : string)
      := mkPwMgrStack
           (SSB.serverSyncBox (fun s1 s2 => if string_dec s1 s2 then true else false) initStore)
           WB.warningBox
           UI.ui
           (fun world handle => net world handle storageId).


    Lemma pwMgrLoop_eta ssb wb ui net
    : pwMgrLoop ssb wb ui net = Step (pwMgrLoopBody pwMgrLoop ssb wb ui net).
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

    Theorem pwMgrGood initStore storageId :
      emptiesStackForever
        (mkPwMgrStack
           (SSB.serverSyncBox (fun s1 s2 => if string_dec s1 s2 then true else false) initStore)
           WB.warningBox
           UI.ui
           (fun world handle => net world handle storageId)).
    Proof.
      unfold mkPwMgrStack.
      rewrite pwMgrLoop_eta.
      (*
    eapply pwMgrGood'.
       *)
      admit.
    Qed.


    Definition initStore := "".
    (** We should do something sane here, not use "foo" unconditionally. *)
    Definition storageId := "foo".

    Definition proc
      := (consoleIn sys pwMgrConsoleIn, runStackProcess (pwMgrStack initStore storageId) (pwMgrGood initStore storageId)).

  End pwMgr.
End MakePwMgr.
