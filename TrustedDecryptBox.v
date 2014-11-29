(** * A box to decrypt data (part of TCB) *)
Require Import Coq.Program.Basics Coq.Strings.String.
Require Import FunctionApp EncryptionInterface.

Local Open Scope program_scope.

Set Implicit Arguments.

(** ** Summary

    We implement a box that decrypts data:

<<
                      ┌─────────┐
    encrypted data in │         │
    ----------------> │         │ unencrypted data out
                      │ Decrypt │ -------------------->
    set master key    │   Box   │
    ----------------> │         │
                      │         │
                      └─────────┘

>> *)

Module TrustedDecryptBox (DataTypes : EncryptionDataTypes) (Algorithm : EncryptionAlgorithm DataTypes).
  Import DataTypes.

  Section trustedDecryptBox.
    (** Because the box is asynchronous, we enable tagging data with
        identifiers.  The identifiers are passed unchanged with the
        encrypted data. *)

    Variable dataTagT : Type.

    Record DecryptBoxState :=
      { masterKey : option { key : masterKeyT | Algorithm.isValidMasterKey key = true } }.

    Inductive dbInput :=
    | dbSetMasterKey (key : masterKeyT)
    | dbDecrypt (encryptedData : encryptedDataT) (tag : dataTagT).

    Inductive dbErrorOutput :=
    | dbErrorInvalidData (data : encryptedDataT) (tag : dataTagT)
    | dbErrorInvalidMasterKey (key : masterKeyT) (pf : Algorithm.isValidMasterKey key = false)
    | dbErrorNoMasterKey.

    Inductive dbEventOutput :=
    | dbDecrypted (data : rawDataT) (tag : dataTagT).

    Definition dbOutput := (dbErrorOutput + dbEventOutput)%type.

    Context (world : Type)
            (handle : dbOutput -> action world).

    Definition initState : DecryptBoxState :=
      {| masterKey := None |}.

    Definition decryptBoxLoopPreBody
               (st : DecryptBoxState)
    : dbInput -> option dbOutput * DecryptBoxState
      := fun i =>
           match i with

             | dbSetMasterKey key
               => (if Algorithm.isValidMasterKey key as isValid return Algorithm.isValidMasterKey key = isValid -> _
                   then fun pf => (None,
                                   {| masterKey := Some (exist _ key pf) |})
                   else fun pf => (Some (inl (@dbErrorInvalidMasterKey key pf)),
                                   {| masterKey := None |})) eq_refl

             | dbDecrypt data tag
               => (match st.(masterKey) with
                     | None => Some (inl dbErrorNoMasterKey)
                     | Some (exist key pf)
                       => match Algorithm.decrypt key pf data with
                            | inl rawData => Some (inr (dbDecrypted rawData tag))
                            | inr InvalidEncryptedData => Some (inl (dbErrorInvalidData data tag))
                          end
                   end,
                   st)
           end.

    Definition decryptBoxLoopBody {T}
               (decryptBoxLoop : DecryptBoxState -> T)
               (st : DecryptBoxState)
    : dbInput -> action world * T
      := fun i => let outs := fst (decryptBoxLoopPreBody st i) in
                  (match outs with
                     | None => id
                     | Some out => handle out
                   end,
                   decryptBoxLoop (snd (decryptBoxLoopPreBody st i))).

    CoFixpoint decryptBoxLoop (st : DecryptBoxState) :=
      Step (decryptBoxLoopBody decryptBoxLoop st).

    Definition decryptBox : process _ _ := decryptBoxLoop initState.
  End trustedDecryptBox.
End TrustedDecryptBox.
