(** * A box to mirror a server over untrusted channels using encryption while preventing timing side channels (part of TCB) *)
Require Import Coq.Program.Basics Coq.Numbers.Natural.Peano.NPeano Coq.Lists.List.
Require Import FunctionApp EncryptionInterface TrustedTickBox TrustedEncryptBox TrustedDecryptBox.
Require Import Common.

Local Open Scope list_scope.
Local Open Scope program_scope.

Set Implicit Arguments.

(** ** Summary

    We implement a box that presents the interface of a server storing
    unencrypted data.  It handles "compare and set" and "get"
    requests, and raises "compare and set failed locally (returns
    current state)", "compare and set succeeded locally", and "remote
    conflict (returns desired state, current state, and common
    ancestor)", and "updated current state".  The "compare and set"
    operation accepts keys of any type, which allows the client to
    correlate "compare and set" requests with their responses.
    Additionally, we provide read access to the current state of the
    remote server, and an "are we fully synced?"  boolean.

    We maintain the following internal state:
    - [remoteStateE] - state we think the remote server has right now (encrypted)
    - [remoteStateD] - state we think the remote server has right now (decrypted)
    - [localStateD] - state we want the remote server to have (decrypted)

    We implement the following straight-forward events:

    Client Events:

    - [ssbClientGetUpdate] - When the client requests an
      update from the server, we request an update from our remote
      server, hidden behind a tick box.

    - [ssbClientGetRemoteState of getRemoteKeyT] - When the client
      wants to know the state of the remote server, we return
      [remoteStateD].

    - [ssbClientAskIsFullySynced of fullySyncedKeyT] - When the client
      wants to know if we are fully synced, we return [localStateD =
      remoteStateD].

    - [ssbClientCompareAndSet of (curD newD : rawDataT) (key :
      clientCASKeyT)] - When the client requests a compare and set, we
      set [localStateD] to [newD] iff it was previously [curD].  On
      success, we raise [ssbCASLocalSuccess key], and on failure, we
      raise [ssbCASLocalFailure key localStateD].  We then schedule a
      server CAS.

    Server Events:

    - [ssbServerGotUpdate (newE : encryptedDataT)] - When the server
      provides us with an update, we decrypt it to [newD].  If we
      fail, we inform the client that the remote server got messed up.
      If we succeed, and it is different from [localStateD], we set
      [localStateD] and [remoteStateD] to [newD], and push an update
      to the client.  In all cases, we set [remoteStateE] to [newE].

    Timed events:

    - When it's time to do a server CAS, we compute an encryption
      [localStateE] of [localStateD].  We then tell the server that if
      it's state is [remoteStateE], it should replace it with
      [localStateE].

      - On success, we set [remoteStateE] to [localStateE] and
        [remoteStateD] to [localStateD] (values all taken at time of
        encryption).

      - On failure (current state is [remoteStateE']), we attempt to
        decrypt to [remoteStateD'].

        - On decryption succeess, we set [remoteStateE] to
          [remoteStateE'], and [remoteStateD] to [remoteStateD'].  We
          then alert the client that there was a remote conflict
          between [remoteStateD] (taken at time of encryption) and
          [remoteStateD'], when trying to update [remoteStateD] to
          [localStateD] (both taken at time of encryption).

        - On decryption failure, set [remoteStateE] to
          [remoteStateE'], clear [remoteStateD], and inform the client
          that the remote server got messed up.

  *)

Module TrustedServerSyncBox (DataTypes : EncryptionDataTypes) (Algorithm : EncryptionAlgorithm DataTypes).
  Import DataTypes.

  Module Import TEB := TrustedEncryptBox DataTypes Algorithm.
  Module Import TDB := TrustedDecryptBox DataTypes Algorithm.

  Section trustedServerSyncBox.
    Variables getRemoteKeyT fullySyncedKeyT clientCASKeyT : Type.
    Variable d_eqb : rawDataT -> rawDataT -> bool.

    Record ServerSyncBoxPreState
      := { localStateD : rawDataT;
           remoteStateD : option rawDataT;
           remoteStateE : option encryptedDataT }.

    (** snapshot of state at time of encryption request *)
    Let encryptDataTagT := ServerSyncBoxPreState.
    Let pre_cas_state := encryptDataTagT.
    (** (curE, newE) *)
    Let cas_state := ((encryptedDataT * encryptedDataT) * pre_cas_state)%type.
    Inductive ssbDecryptTagT :=
    | ssbDTGotUpdate (dataE : encryptedDataT)
    | ssbDTCASFailure (frozenState : ServerSyncBoxPreState) (remoteE : encryptedDataT)
    | ssbDTCASSuccess (frozenState : ServerSyncBoxPreState) (remoteE : encryptedDataT).

    Record ServerSyncBoxState :=
      {
        ssbState :> ServerSyncBoxPreState;
        ssbGetUpdateState : TickBoxState unit;
        ssbCASState : TickBoxState cas_state;
        ssbEncryptState : EncryptBoxState;
        ssbDecryptState : DecryptBoxState
      }.

(* python:
<<
fields=[(x.strip(), y.strip()) for x, y in [z.split(':') for z in """
        ssbState : ServerSyncBoxPreState;
        ssbGetUpdateState : TickBoxState unit;
        ssbCASState : TickBoxState cas_state;
        ssbEncryptState : EncryptBoxState;
        ssbDecryptState : DecryptBoxState""".split(';')]]
for field0, ty0 in fields:
    body = ';\n          '.join((('%s := st.(%s)' % (field, field)) if field != field0 else ('%s := v' % field))
                                for field, ty in fields)
    print('  Definition set_%s (st : ServerSyncBoxState) (v : %s)' % (field0, ty0))
    print('    := {| ' + body + ' |}.\n')
>> *)

    Definition set_ssbState (st : ServerSyncBoxState) (v : ServerSyncBoxPreState)
      := {| ssbState := v;
            ssbGetUpdateState := st.(ssbGetUpdateState);
            ssbCASState := st.(ssbCASState);
            ssbEncryptState := st.(ssbEncryptState);
            ssbDecryptState := st.(ssbDecryptState) |}.

    Definition set_ssbGetUpdateState (st : ServerSyncBoxState) (v : TickBoxState unit)
      := {| ssbState := st.(ssbState);
            ssbGetUpdateState := v;
            ssbCASState := st.(ssbCASState);
            ssbEncryptState := st.(ssbEncryptState);
            ssbDecryptState := st.(ssbDecryptState) |}.

    Definition set_ssbCASState (st : ServerSyncBoxState) (v : TickBoxState cas_state)
      := {| ssbState := st.(ssbState);
            ssbGetUpdateState := st.(ssbGetUpdateState);
            ssbCASState := v;
            ssbEncryptState := st.(ssbEncryptState);
            ssbDecryptState := st.(ssbDecryptState) |}.

    Definition set_ssbEncryptState (st : ServerSyncBoxState) (v : EncryptBoxState)
      := {| ssbState := st.(ssbState);
            ssbGetUpdateState := st.(ssbGetUpdateState);
            ssbCASState := st.(ssbCASState);
            ssbEncryptState := v;
            ssbDecryptState := st.(ssbDecryptState) |}.

    Definition set_ssbDecryptState (st : ServerSyncBoxState) (v : DecryptBoxState)
      := {| ssbState := st.(ssbState);
            ssbGetUpdateState := st.(ssbGetUpdateState);
            ssbCASState := st.(ssbCASState);
            ssbEncryptState := st.(ssbEncryptState);
            ssbDecryptState := v |}.

    Inductive ssbConfigInput :=
    | ssbGetUpdateConfig (_ : tbConfigInput)
    | ssbCASConfig (_ : tbConfigInput)
    | ssbSetMasterKey (key : masterKeyT).

    Inductive ssbEventInput :=
    | ssbTick (addedTickCount : nat)
    | ssbClientGetUpdate
    | ssbClientGetRemoteState (key : getRemoteKeyT)
    | ssbClientAskIsFullySynced (key : fullySyncedKeyT)
    | ssbClientCompareAndSet (key : clientCASKeyT) (curD newD : rawDataT)
    | ssbServerGotUpdate (newE : encryptedDataT)
    | ssbServerCASFailure (key : pre_cas_state) (claimedCurE realCurE newE : encryptedDataT)
    | ssbServerCASSuccess (key : pre_cas_state) (newE : encryptedDataT)
    | ssbSystemRandomness (randomness : systemRandomnessT) (tag : rawDataT * encryptDataTagT).


    Definition ssbInput := (ssbConfigInput + ssbEventInput)%type.

    Inductive ssbWarningOutput :=
    | ssbGetUpdateWarning (_ : tbWarningOutput unit)
    | ssbCASWarning (_ : tbWarningOutput cas_state)
    | ssbEncryptError (_ : ebErrorOutput)
    | ssbDecryptError (_ : dbErrorOutput ssbDecryptTagT)
    | ssbWarningInvalidTransition (ev : ssbInput) (st : ServerSyncBoxState)
    | ssbErrorNoCASBeforeGetUpdate.

    Inductive ssbEventOutput :=
    | ssbClientGotUpdate (data : rawDataT)
    | ssbClientGotRemoteState (key : getRemoteKeyT) (data : option rawDataT)
    | ssbClientRespondIsFullySynced (key : fullySyncedKeyT) (_ : bool)
    | ssbClientCASSuccess (key : clientCASKeyT) (newD : rawDataT)
    | ssbClientCASFailure (key : clientCASKeyT) (claimedCurD realCurD newD : rawDataT)
    | ssbClientRemoteConflict (localD remoteD : rawDataT) (ancestorD : option rawDataT)
    | ssbClientRemoteUpdateSuccess (oldD newD : rawDataT)
    | ssbServerGetUpdate
    | ssbServerCAS (key : pre_cas_state) (curE newE : encryptedDataT)
    | ssbRequestSystemRandomness (howMuch : systemRandomnessHintT) (tag : rawDataT * encryptDataTagT).

    Definition ssbOutput := (ssbWarningOutput + ssbEventOutput)%type.

    Variable initRawData : rawDataT.
    Context (world : Type)
            (handle : ssbOutput -> action world).

    Definition initState : ServerSyncBoxState :=
      {|
        ssbState := {| localStateD := initRawData;
                       remoteStateD := None;
                       remoteStateE := None |};
        ssbGetUpdateState := TrustedTickBox.initState _;
        ssbCASState := TrustedTickBox.initState _;
        ssbEncryptState := TEB.initState;
        ssbDecryptState := TDB.initState
      |}.

    Local Ltac handle_eq_false' :=
      idtac;
      match goal with
        | _ => progress subst_body
        | _ => intro
        | _ => progress simpl in *
        | [ H : appcontext[match ?E with _ => _ end] |- _ ] => (atomic E; destruct E)
        | [ H : Some _ = None |- _ ] => solve [ inversion H ]
        | [ H : None = Some _ |- _ ] => solve [ inversion H ]
        | [ H : inl _ = inr _ |- _ ] => solve [ inversion H ]
        | [ H : inr _ = inl _ |- _ ] => solve [ inversion H ]
        | [ H : _::_ = nil |- _ ] => solve [ inversion H ]
        | [ H : appcontext[match ?E with _ => _ end] |- _ ] => (revert H; case_eq E; intros)
        | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
        | [ H : inl _ = inl _ |- _ ] => inversion H; clear H
        | [ H : inr _ = inr _ |- _ ] => inversion H; clear H
        | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
        | [ H : _::_ = _::_ |- _ ] => inversion H; clear H
      end.

    Local Ltac handle_eq_false :=
      match goal with
        | [ |- _ -> False ] => idtac
      end;
      subst_body; clear; intro;
      abstract (repeat handle_eq_false').

    Definition handle_ssbGetUpdate'
               (st : ServerSyncBoxState)
    : tbOutput unit * TickBoxState unit -> list ssbOutput * ServerSyncBoxState.
    Proof.
      refine (fun i =>
                (match fst i with
                   | inl warning
                     => inl (ssbGetUpdateWarning warning)::nil
                   | inr tbRequestDataUpdate
                     => let upd := tickBoxLoopPreBody
                                     (st.(ssbGetUpdateState))
                                     (inr (tbValueReady tt)) in
                        match fst upd as u return u = fst upd -> _ with
                          | nil => fun _ => nil
                          | inl warning::nil => fun _ => inl (ssbGetUpdateWarning warning)::nil
                          | _ => fun H => match (_ H) : False with end
                        end eq_refl
                   | inr (tbPublishUpdate val)
                     => inr ssbServerGetUpdate::nil
                 end,
                 set_ssbGetUpdateState st (snd i)));
      handle_eq_false.
    Defined.

    Definition fold_handler {outT stT}
               (get : ServerSyncBoxState -> stT)
               (set : ServerSyncBoxState -> stT -> ServerSyncBoxState)
               (handle : ServerSyncBoxState -> outT * stT -> list ssbOutput * ServerSyncBoxState)
               (st : ServerSyncBoxState)
    : list outT * stT -> list ssbOutput * ServerSyncBoxState
      := fun outs_st =>
           fold_left (fun ls_st out =>
                        let ls'_st' := handle (snd ls_st) (out, get (snd ls_st)) in
                        (fst ls_st ++ fst ls'_st', snd ls'_st'))
                     (fst outs_st)
                     (nil, set st (snd outs_st)).

    Definition handle_ssbGetUpdate
      := fold_handler ssbGetUpdateState set_ssbGetUpdateState handle_ssbGetUpdate'.

    Definition handle_ssbEncrypt
               (st : ServerSyncBoxState)
    : option (ebOutput encryptDataTagT) * EncryptBoxState -> list ssbOutput * ServerSyncBoxState.
    Proof.
      refine (fun i =>
                let st' := set_ssbEncryptState st (snd i) in
                (match fst i with
                   | Some (inl warning)
                     => inl (ssbEncryptError warning)::nil
                   | Some (inr (ebRequestSystemRandomness howMuch tag))
                     => (inr (ssbRequestSystemRandomness howMuch tag))::nil
                   | Some (inr (ebEncrypted newE frozenState))
                     => match frozenState.(remoteStateE) with
                          | Some curE
                            => (inr (ssbServerCAS frozenState curE newE))::nil
                          | None => (inl ssbErrorNoCASBeforeGetUpdate)::nil
                        end
                   | None => nil
                 end,
                 st')).
    Defined.

    Definition handle_ssbCAS'
               (st : ServerSyncBoxState)
    : tbOutput cas_state * TickBoxState cas_state -> list ssbOutput * ServerSyncBoxState.
    Proof.
      refine (fun i =>
                let st' := set_ssbCASState st (snd i) in
                match fst i with
                  | inl warning
                    => (inl (ssbCASWarning warning)::nil, st')
                  | inr (tbPublishUpdate val)
                    => (inr ssbServerGetUpdate::nil, st')

                  | inr tbRequestDataUpdate

                    (** request an encryption of the current state, and
                      snapshot the current state so we can decide what
                      to do when we get back the encrypted value *)

                    => let encResult := encryptBoxLoopPreBody
                                          (st.(ssbEncryptState))
                                          (ebEncrypt (st.(localStateD)) (st.(ssbState))) in
                       handle_ssbEncrypt st' encResult
                end).
    Defined.

    Definition handle_ssbCAS
      := fold_handler ssbCASState set_ssbCASState handle_ssbCAS'.

    Definition handle_ssbDecrypt
               (st : ServerSyncBoxState)
    : option (dbOutput ssbDecryptTagT) * DecryptBoxState -> list ssbOutput * ServerSyncBoxState.
    Proof.
      refine (fun i =>
                let st' := set_ssbDecryptState st (snd i) in
                match fst i with

                  | Some (inl warning)
                    => (inl (ssbDecryptError warning)::nil,
                        set_ssbState
                          st'
                          ({| localStateD := st'.(localStateD);
                              remoteStateD := None;
                              remoteStateE :=
                                (match warning with
                                   | dbErrorInvalidData dataE _
                                     => Some dataE
                                   | _ => None
                                 end) |}))

                  | Some (inr (dbDecrypted dataD (ssbDTGotUpdate dataE)))
                    => ((if d_eqb dataD st.(localStateD)
                         then nil
                         else (inr (ssbClientGotUpdate dataD))::nil),
                        set_ssbState st' {| localStateD := dataD;
                                            remoteStateD := Some dataD;
                                            remoteStateE := Some dataE |})

                  | Some (inr (dbDecrypted remoteD (ssbDTCASFailure frozenState dataE)))
                    => ((inr (ssbClientRemoteConflict
                                (frozenState.(localStateD)) (* local *)
                                remoteD
                                (frozenState.(remoteStateD)) (* ancestor *)))::nil,
                        set_ssbState st' {| localStateD := remoteD;
                                            remoteStateD := Some remoteD;
                                            remoteStateE := Some dataE |})

                  | Some (inr (dbDecrypted remoteD (ssbDTCASSuccess frozenState dataE)))
                    => ((inr (ssbClientRemoteUpdateSuccess
                                (frozenState.(localStateD)) (* oldD *)
                                remoteD (* newD *)))::nil,
                        set_ssbState st' {| localStateD := remoteD;
                                            remoteStateD := Some remoteD;
                                            remoteStateE := Some dataE |})

                  | None => (nil, st')

                end).
    Defined.

    Definition serverSyncBoxLoopPreBody
               (st : ServerSyncBoxState)
    : ssbInput -> list ssbOutput * ServerSyncBoxState.
    Proof.
      refine (fun i =>
                match i with

                  | inl (ssbGetUpdateConfig i')
                    => handle_ssbGetUpdate
                         st
                         (tickBoxLoopPreBody
                            (st.(ssbGetUpdateState))
                            (inl i'))

                  | inl (ssbCASConfig i')
                    => handle_ssbCAS
                         st
                         (tickBoxLoopPreBody
                            (st.(ssbCASState))
                            (inl i'))

                  | inl (ssbSetMasterKey newKey)
                    => let (ls0, st0) := handle_ssbEncrypt
                                           st
                                           (encryptBoxLoopPreBody
                                              (st.(ssbEncryptState))
                                              (ebSetMasterKey _ newKey)) in
                       let (ls1, st1) := handle_ssbDecrypt
                                           st
                                           (decryptBoxLoopPreBody
                                              (st.(ssbDecryptState))
                                              (dbSetMasterKey _ newKey)) in
                       (ls0 ++ ls1, st1)

                  | inr (ssbTick addedTickCount)
                    => let (ls0, st0) := handle_ssbGetUpdate
                                           st
                                           (tickBoxLoopPreBody
                                              (st.(ssbGetUpdateState))
                                              (inr (tbTick _ addedTickCount))) in
                       let (ls1, st1) := handle_ssbCAS
                                           st0
                                           (tickBoxLoopPreBody
                                              (st0.(ssbCASState))
                                              (inr (tbTick _ addedTickCount))) in
                       (ls0 ++ ls1, st1)

                  | inr ssbClientGetUpdate
                    => handle_ssbGetUpdate
                         st
                         (tickBoxLoopPreBody
                            (st.(ssbGetUpdateState))
                            (inr (tbNotifyChange _)))

                  | inr (ssbClientGetRemoteState key)
                    => ((inr (ssbClientGotRemoteState key (st.(remoteStateD))))::nil, st)

                  | inr (ssbClientAskIsFullySynced key)
                    => let b := match st.(remoteStateD) with
                                  | None => false
                                  | Some remoteStateD' => d_eqb st.(localStateD) remoteStateD'
                                end in
                       ((inr (ssbClientRespondIsFullySynced key b))::nil, st)

                  | inr (ssbClientCompareAndSet key curD newD)
                    => if d_eqb st.(localStateD) curD
                       then (let st' := set_ssbState
                                          st
                                          {| localStateD := newD;
                                             remoteStateD := st.(remoteStateD);
                                             remoteStateE := st.(remoteStateE) |} in
                             let (ls0, st0) := handle_ssbCAS
                                                 st'
                                                 (tickBoxLoopPreBody
                                                    (st'.(ssbCASState))
                                                    (inr (tbNotifyChange _))) in
                             ((inr (ssbClientCASSuccess key newD))::ls0, st0))
                       else ((inr (ssbClientCASFailure key curD st.(localStateD) newD))::nil, st)

                  | inr (ssbServerGotUpdate dataE)
                    => handle_ssbDecrypt
                         st
                         (decryptBoxLoopPreBody
                            (st.(ssbDecryptState))
                            (dbDecrypt dataE (ssbDTGotUpdate dataE)))

                  | inr (ssbServerCASFailure frozenState claimedCurE realCurE newE)
                    => handle_ssbDecrypt
                         st
                         (decryptBoxLoopPreBody
                            (st.(ssbDecryptState))
                            (dbDecrypt realCurE (ssbDTCASFailure frozenState realCurE)))

                  | inr (ssbServerCASSuccess frozenState newE)
                    => handle_ssbDecrypt
                         st
                         (decryptBoxLoopPreBody
                            (st.(ssbDecryptState))
                            (dbDecrypt newE (ssbDTCASSuccess frozenState newE)))

                  | inr (ssbSystemRandomness randomness tag)
                    => handle_ssbEncrypt
                         st
                         (encryptBoxLoopPreBody
                            (st.(ssbEncryptState))
                            (ebSystemRandomness randomness tag))

                end).
    Defined.

    Definition serverSyncBoxLoopBody {T}
               (serverSyncBoxLoop : ServerSyncBoxState -> T)
               (st : ServerSyncBoxState)
    : ssbInput -> action world * T
      := fun i => let outs := fst (serverSyncBoxLoopPreBody st i) in
                  (fold_left compose (map handle outs) id,
                   serverSyncBoxLoop (snd (serverSyncBoxLoopPreBody st i))).

    CoFixpoint serverSyncBoxLoop (st : ServerSyncBoxState) :=
      Step (serverSyncBoxLoopBody serverSyncBoxLoop st).

    Definition serverSyncBox : process _ _ := serverSyncBoxLoop initState.
  End trustedServerSyncBox.
End TrustedServerSyncBox.
