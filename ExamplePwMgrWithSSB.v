Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Program.Basics Coq.Program.Program Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Coq.NArith.BinNat.
Require Import SerializableMergableFMapInterface StringKey PrefixSerializable.
Require Import System FunctionApp FunctionAppLemmas FunctionAppTactics.
Require Import PwMgrUI PwMgrWarningBox PwMgrNet TrustedServerSyncBox EncryptionInterface TickGenerator.
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
         | SSB.ssbTick n                 => WB.SSB.ssbTick n
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
    | pwMgrFatal (msg : string)
    | pwMgrConfigure (debug : N)
    | pwMgrInit (key : string)
    | pwMgrConsoleIn (line : string)
    | pwUI (msg : UI.uiInput)
    | pwW (msg : WB.wInput)
    | pwSSB (msg : SSB.ssbInput)
    | pwNET (msg : netInput)
    | pwTG (msg : tickGInput).

    Context (world : Type).
    Context (sys : systemActions input world).

    Definition one_second := 1000000000%N.

    Definition abort msg := sys.(consoleErr) msg ∘ sys.(exit) 255.
    CoFixpoint hang {input world} := Step (fun (_ : input) => (@id world, hang)).

    Definition pwMgrLoopBody pwMgrLoop ssb wb ui net tickG
    : input -> action (stackWorld input world) * stackProcess input world :=
      fun i =>
        match i with
          | pwMgrFatal msg => (stackLift (abort msg), hang)
          | pwMgrConfigure _ => (stackLift (abort "UNEXPECTED INPUT"), hang)
          | pwMgrInit key => (stackPush (pwSSB (inl (SSB.ssbSetMasterKey key))) ∘ stackPush (pwNET netGetUpdate) ∘ stackLift (sys.(sleepNanosecs) one_second (pwTG TGWakeUp)), pwMgrLoop ssb wb ui net tickG)
          | pwMgrConsoleIn s =>
            (stackPush (pwUI (UI.uiConsoleIn s)) ∘ stackLift (sys.(consoleIn) pwMgrConsoleIn), pwMgrLoop ssb wb ui net tickG)
          | pwNET ev => let (a, net') := getStep net ev in (a, pwMgrLoop ssb wb ui net' tickG)
          | pwUI ev  => let (a, ui')  := getStep ui  ev in (a, pwMgrLoop ssb wb ui' net tickG)
          | pwW ev   => let (a, wb')  := getStep wb  ev in (a, pwMgrLoop ssb wb' ui net tickG)
          | pwSSB ev => let (a, ssb') := getStep ssb ev in (a, pwMgrLoop ssb' wb ui net tickG)
          | pwTG ev  => let (a, tickG') := getStep tickG ev in (a, pwMgrLoop ssb wb ui net tickG')
        end.

    CoFixpoint pwMgrLoop ssb wb ui net tickG : stackProcess input world :=
      Step (pwMgrLoopBody pwMgrLoop ssb wb ui net tickG).

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
      wb (world' := stackWorld input world)
        (fun i =>
           match i with
             | WB.wConsoleErr lines
               => stackLift (sys.(consoleErr) lines)
             | WB.wBad msg
               => stackLift (abort msg)
             | WB.wFatalError msg
               => stackLift (abort msg)
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
               => stackLift (sys.(getRandomness) (N.of_nat howMuch) (pwSSB ∘ inr ∘ SSB.ssbSystemRandomness tag))
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
                 => stackLift (httpPOST sys uri data (fun r => pwNET (cb r)))
             end).

    Definition
      wrap_tickG
      (tickG :
         forall {world'},
           (tickGOutput -> action world') ->
           process tickGInput world') :=
      tickG (fun i =>
             match i with
               | TGSleepNanosecs n
                 => stackLift (sys.(sleepNanosecs) n (pwTG TGWakeUp))
               | TGGetNanosecs
                 => stackLift (sys.(getNanosecs) (pwTG ∘ TGClocksGot))
               | TGTick n
                 => stackPush (pwSSB (inr (SSB.ssbTick n): SSB.ssbInput))
             end).

    Definition
      mkPwMgrStack ssb wb ui net tickG :
      stackProcess input world :=
      pwMgrLoop (wrap_ssb ssb) (wrap_wb wb) (wrap_ui ui) (wrap_net net) (wrap_tickG tickG).

    Definition pwMgrStack (initStore : EncryptionStringDataTypes.rawDataT) (storageId : string) (debug : N)
      := mkPwMgrStack
           (SSB.serverSyncBox (fun s1 s2 => if string_dec s1 s2 then true else false) initStore)
           (fun world handle => WB.warningBox world handle debug)
           UI.ui
           (fun world handle => net world handle storageId).


    Lemma pwMgrLoop_eta ssb wb ui net tickG
    : pwMgrLoop ssb wb ui net tickG = Step (pwMgrLoopBody pwMgrLoop ssb wb ui net tickG).
    Proof.
      rewrite stackProcess_eta at 1; reflexivity.
    Qed.
(*
    CoFixpoint pwMgrGood' : 
      forall ssbState uiState debug storageId,
        emptiesStackForever
          (Step
             (pwMgrLoopBody 
                pwMgrLoop
                (wrap_ssb
                   (SSB.serverSyncBox
                      (fun s1 s2 : EncryptionStringDataTypes.rawDataT =>
                         if string_dec s1 s2 then true else false) ssbState))
                (wrap_wb (fun world handle => @WB.warningBox world handle debug)) 
                (wrap_ui (fun world handle => @UI.uiLoop world handle uiState))
                (wrap_net
                   (fun (world : Type) (handle : netOutput -> action world) =>
                      net world handle storageId)))).
    Proof.
      intro; constructor.
      let tac := (idtac; 
                  match goal with
                    | [ |- appcontext[match split ?a ?b with _ => _ end] ] => destruct (split a b)
                    | [ |- appcontext[match string_dec ?s0 ?s1 with _ => _ end] ] => destruct (string_dec s0 s1)
                    | [ |- appcontext[match ?l with nil => _ | _ => _ end] ] => destruct l
                    | [ |- appcontext[match find ?f ?ls with _ => _ end] ] => destruct (find f ls)
                    | [ |- appcontext[match ?x with (_, _) => _ end] ] => rewrite (@surjective_pairing _ _ x)
                    | [ |- appcontext[match ?a with (pwMgrNetInput _) => _ | _ => _ end] ] => destruct a
                    | [ |- appcontext[match ?a with None => _ | _ => _ end] ] => destruct a
                    | [ |- appcontext[match dec ?b with _ => _ end] ] => destruct (dec b)
                    | _ => progress unfold storageSet in *
                  end) in
      emptiesStackForever_t pwMgrGood' input (@pwMgrLoop_eta) (@pwMgrLoop) tac.
      Focus 3.
      {
        eapply emptiesStackDone.
        econstructor.
      Admitted.
*)
    Theorem pwMgrGood initStore storageId (debug : N) :
      emptiesStackForever
        (mkPwMgrStack
           (SSB.serverSyncBox (fun s1 s2 => if string_dec s1 s2 then true else false) initStore)
           (fun world handle => WB.warningBox world handle debug)
           UI.ui
           (fun world handle => net world handle storageId)
           tickG
        ).
    Proof.
      unfold mkPwMgrStack.
      rewrite pwMgrLoop_eta.
      (* eapply pwMgrGood'. *)
      admit.
    Qed.

    Definition initStore := "".
    (** We should do something sane here, not use "foo" unconditionally. *)
    Definition storageId := "foo".

    CoFixpoint getMasterKeyLoop debug :=
      Step (fun i =>
              match i with
                | pwMgrConsoleIn key =>
                  match runStackProcess (pwMgrStack initStore storageId debug tickG) (pwMgrGood initStore storageId debug) with
                    | Step f =>
                      let (a, p) := f (pwMgrInit key) in
                      (consoleIn sys pwMgrConsoleIn ∘ a, p)
                  end
                | _ => (abort "UNEXPECTED INPUT", hang)
              end).

    Definition getMasterKey debug
      := (consoleOut sys "Enter your master key:" ∘ consoleIn sys pwMgrConsoleIn, getMasterKeyLoop debug).

    Fixpoint parseFlag argv0 debug flag next :=
      match flag with
        | EmptyString => next debug
        | (String "d" flag') => parseFlag argv0 (debug + 1)%N flag' next
        | _ => pwMgrFatal ("usage: " ++ argv0)
      end.

    Fixpoint parseArgv' argv0 argv debug :=
      match argv with
        | nil => pwMgrConfigure debug
        | (String "-" flag) :: argv' => parseFlag argv0 debug flag (parseArgv' argv0 argv')
        | _ => pwMgrFatal ("usage: " ++ argv0 ++ " [-d...]")
      end.

    Definition parseArgv debug argv :=
      match argv with
        | nil => pwMgrFatal "EMPTY ARGV"
        | argv0 :: argv' => parseArgv' argv0 argv' debug
      end.

    Definition proc : action world * process input world :=
      (sys.(getArgv) (parseArgv 0),
       Step (fun i =>
               match i with
                 | pwMgrFatal msg => (abort msg, hang)
                 | pwMgrConfigure debug => getMasterKey debug
                 | _ => (abort "UNEXPECTED INPUT", hang)
               end)).

  End pwMgr.
End MakePwMgr.
