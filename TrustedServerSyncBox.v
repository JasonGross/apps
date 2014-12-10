(** * A box to mirror a server over untrusted channels using encryption while preventing timing side channels (part of TCB) *)
Require Import Coq.Program.Basics Coq.NArith.NArith Coq.Lists.List.
Require Import FunctionApp EncryptionInterface TrustedTickBox TrustedEncryptBox TrustedDecryptBox.
Require Import Common.

Local Open Scope list_scope.
Local Open Scope program_scope.

Set Implicit Arguments.

(** ** Summary

    We implement a box that presents the interface of a server storing
    unencrypted data.  It handles "set" and "get eventually" requests,
    and raises "value changed" and "remote corrupted".

    We assume the remote server has a "compare and set" event; we use
    this to be robust to update messages lost over the network.  It is
    the client's responsibility to set up the tick-box intervals so
    that we get an updated server value sufficiently close to our
    sending that CAS succeeds.

    We maintain the following internal state:
    - [remoteStateE] - state we think the remote server has right now (encrypted)
    - [localStateD] - state we want the remote server to have (decrypted)

    We implement the following events:

    Client Events:

    - [ssbClientGetUpdate] - When the client requests an
      update from the server, we request an update from our remote
      server, hidden behind a tick box.

    - [ssbClientSet (newD : rawDataT)] - When the client requests a
      SET, we set [localStateD] to [newD], and schedule a remote
      update.

    Server Events:

    - [ssbServerGotUpdate (newE : encryptedDataT)] - When the server
      provides us with an update, we decrypt it to [newD].  If we
      fail, we inform the client that the remote server got messed up.
      If we succeed, and it is different from [localStateD], we set
      [localStateD] to [newD], and push an update to the client.  In
      all cases, we set [remoteStateE] to [newE].

    Timed events:

    - When it's time to do a server CAS, we compute an encryption
      [localStateE] of [localStateD].  We then tell the server that if
      it's state is [remoteStateE], it should replace it with
      [localStateE].  The server is expected to respond with
      [ssbServerGotUpdate] with it's updated state on both failure and
      success.

  *)

Module TrustedServerSyncBox (DataTypes : EncryptionDataTypes) (Algorithm : EncryptionAlgorithm DataTypes).
  Import DataTypes.

  Module Import TEB := TrustedEncryptBox DataTypes Algorithm.
  Module Import TDB := TrustedDecryptBox DataTypes Algorithm.

  Section trustedServerSyncBox.
    Variable d_eqb : rawDataT -> rawDataT -> bool.

    Record ServerSyncBoxPreState
      := { localStateD : rawDataT;
           remoteStateE : option encryptedDataT }.

    Record ServerSyncBoxState :=
      {
        ssbState :> ServerSyncBoxPreState;
        ssbGetUpdateState : TickBoxState unit;
        ssbCASState : TickBoxState encryptedDataT;
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

    Definition set_ssbCASState (st : ServerSyncBoxState) (v : TickBoxState encryptedDataT)
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
    | ssbClientGetUpdate
    | ssbClientSet (newD : rawDataT)
    | ssbServerGotUpdate (newE : encryptedDataT)
    | ssbSystemRandomness (randomness : systemRandomnessT) (tag : rawDataT)
    | ssbTick (_ : N).

    Definition ssbInput := (ssbConfigInput + ssbEventInput)%type.

    Inductive ssbWarningOutput :=
    | ssbGetUpdateWarning (_ : tbWarningOutput unit)
    | ssbCASWarning (_ : tbWarningOutput encryptedDataT)
    | ssbEncryptError (_ : ebErrorOutput)
    | ssbDecryptError (_ : dbErrorOutput unit)
    | ssbWarningInvalidTransition (ev : ssbInput) (st : ServerSyncBoxState)
    | ssbWarningPushBeforePull.

    Inductive ssbEventOutput :=
    | ssbClientGotUpdate (data : rawDataT)
    | ssbServerGetUpdate
    | ssbServerCAS (curE newE : encryptedDataT)
    | ssbRequestSystemRandomness (howMuch : systemRandomnessHintT) (tag : rawDataT).

    Definition ssbOutput := (ssbWarningOutput + ssbEventOutput)%type.

    Variable initRawData : rawDataT.
    Context (world : Type)
            (handle : ssbOutput -> action world).

    Definition initState : ServerSyncBoxState :=
      {|
        ssbState := {| localStateD := initRawData;
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
        | _ => progress subst
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
        | [ H : ?a = ?b |- _ ]
          => let a' := (eval hnf in a) in
             let b' := (eval hnf in b) in
             progress change (a' = b') in H
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
                          | inl warning::inl warning'::nil => fun _ => inl (ssbGetUpdateWarning warning)::inl (ssbGetUpdateWarning warning')::nil
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
    : option (ebOutput unit) * EncryptBoxState -> list ssbOutput * ServerSyncBoxState.
    Proof.
      refine (fun i =>
                let st' := set_ssbEncryptState st (snd i) in
                match fst i with

                   | Some (inl warning)
                     => ((inl (ssbEncryptError warning))::nil, st')

                   | Some (inr (ebRequestSystemRandomness howMuch tag))
                     => ((inr (ssbRequestSystemRandomness howMuch (fst tag)))::nil, st')

                   | Some (inr (ebEncrypted newE _))
                     => let upd := tickBoxLoopPreBody
                                     (st'.(ssbCASState))
                                     (inr (tbValueReady newE)) in
                        (match fst upd as u return u = fst upd -> _ with
                           | nil => fun _ => nil
                           | inl warning::nil => fun _ => (inl (ssbCASWarning warning))::nil
                           | inl warning::inl warning'::nil => fun _ => inl (ssbCASWarning warning)::inl (ssbCASWarning warning')::nil
                           | _ => fun H => match (_ H) : False with end
                         end eq_refl,
                         set_ssbCASState st' (snd upd))

                   | None => (nil, st')
                 end);
      handle_eq_false.
    Defined.

    Definition handle_ssbCAS'
               (st : ServerSyncBoxState)
    : tbOutput encryptedDataT * TickBoxState encryptedDataT -> list ssbOutput * ServerSyncBoxState.
    Proof.
      refine (fun i =>
                let st' := set_ssbCASState st (snd i) in
                match fst i with
                  | inl warning
                    => (inl (ssbCASWarning warning)::nil, st')

                  | inr (tbPublishUpdate val)
                    => (match st'.(remoteStateE) with
                          | Some curE
                            => inr (ssbServerCAS curE val)
                          | None => inl ssbWarningPushBeforePull
                        end::nil,
                        st')

                  | inr tbRequestDataUpdate
                    => let encResult := encryptBoxLoopPreBody
                                          (st'.(ssbEncryptState))
                                          (ebEncrypt (st.(localStateD)) tt) in
                       handle_ssbEncrypt st' encResult
                end).
    Defined.

    Definition handle_ssbCAS
      := fold_handler ssbCASState set_ssbCASState handle_ssbCAS'.

    Definition handle_ssbDecrypt
               (st : ServerSyncBoxState)
    : option (dbOutput unit) * DecryptBoxState -> list ssbOutput * ServerSyncBoxState.
    Proof.
      refine (fun i =>
                let st' := set_ssbDecryptState st (snd i) in
                match fst i with

                  | Some (inl warning)
                    => (inl (ssbDecryptError warning)::nil, st)

                  | Some (inr (dbDecrypted dataD _))
                    => ((if d_eqb dataD st.(localStateD)
                         then nil
                         else (inr (ssbClientGotUpdate dataD))::nil),
                        set_ssbState st' {| localStateD := dataD;
                                            remoteStateE := st'.(remoteStateE) |})

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
                                           st0
                                           (decryptBoxLoopPreBody
                                              (st.(ssbDecryptState))
                                              (dbSetMasterKey _ newKey)) in
                       (ls0 ++ ls1, st1)

                  | inr (ssbTick n)
                    => let (ls0, st0) := handle_ssbGetUpdate
                                           st
                                           (tickBoxLoopPreBody
                                              (st.(ssbGetUpdateState))
                                              (inr (tbTick _ n))) in
                       let (ls1, st1) := handle_ssbCAS
                                           st0
                                           (tickBoxLoopPreBody
                                              (st0.(ssbCASState))
                                              (inr (tbTick _ n))) in
                       (ls0 ++ ls1, st1)

                  | inr ssbClientGetUpdate
                    => handle_ssbGetUpdate
                         st
                         (tickBoxLoopPreBody
                            (st.(ssbGetUpdateState))
                            (inr (tbNotifyChange _)))

                  | inr (ssbClientSet newD)
                    => let st' := set_ssbState
                                    st
                                    {| localStateD := newD;
                                       remoteStateE := st.(remoteStateE) |} in
                       handle_ssbCAS
                         st'
                         (tickBoxLoopPreBody
                            (st'.(ssbCASState))
                            (inr (tbNotifyChange _)))

                  | inr (ssbServerGotUpdate dataE)
                    => let st' := set_ssbState
                                    st
                                    {| localStateD := st.(localStateD);
                                       remoteStateE := Some dataE |} in
                       handle_ssbDecrypt
                         st'
                         (decryptBoxLoopPreBody
                            (st'.(ssbDecryptState))
                            (dbDecrypt dataE tt))

                  | inr (ssbSystemRandomness randomness tag)
                    => handle_ssbEncrypt
                         st
                         (encryptBoxLoopPreBody
                            (st.(ssbEncryptState))
                            (ebSystemRandomness randomness (tag, tt)))

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
