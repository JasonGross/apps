(** * A box to encrypt data (part of TCB) *)
Require Import Coq.Program.Basics Coq.Strings.String.
Require Import FunctionApp EncryptionInterface.

Local Open Scope program_scope.

Set Implicit Arguments.

(** ** Summary

    We implement a box that encrypts data:

<<
                   System │   ^
               Randomness │   │ Request System Randomness
                          V   │
                        ┌─────────┐
    unencrypted data in │         │
    ------------------> │         │ encrypted data out
                        │ Encrypt │ ------------------>
    set master key      │   Box   │
    ------------------> │         │
                        │         │
                        └─────────┘

>> *)

Module TrustedEncryptBox (DataTypes : EncryptionDataTypes) (Algorithm : EncryptionAlgorithm DataTypes).
  Import DataTypes.

  Section trustedEncryptBox.
    (** Because the box is asynchronous, we enable tagging data with
        identifiers.  The identifiers are passed unchanged with the
        encrypted data.

        Because system randomness is asynchronous, we tag the request
        with the data to encrypt.  Thus, the system randomness handler
        MUST NOT allow the tag to escape the application. *)

    Variable dataTagT : Type.

    Record EncryptBoxState :=
      { masterKey : option { key : masterKeyT | Algorithm.isValidMasterKey key = true } }.

    Inductive ebInput :=
    | ebSetMasterKey (key : masterKeyT)
    | ebSystemRandomness (randomness : systemRandomnessT) (tag : rawDataT * dataTagT)
    | ebEncrypt (unencryptedData : rawDataT) (tag : dataTagT).

    Inductive ebErrorOutput :=
    | ebErrorNotEnoughRandomness (howMuchWanted : systemRandomnessHintT) (randomnessGiven : systemRandomnessT)
    | ebErrorInvalidMasterKey (key : masterKeyT) (pf : Algorithm.isValidMasterKey key = false)
    | ebErrorNoMasterKey.

    Inductive ebEventOutput :=
    | ebRequestSystemRandomness (howMuch : systemRandomnessHintT) (tag : rawDataT * dataTagT)
    | ebEncrypted (data : encryptedDataT) (tag : dataTagT).

    Definition ebOutput := (ebErrorOutput + ebEventOutput)%type.

    Context (world : Type)
            (handle : ebOutput -> action world).

    Definition initState : EncryptBoxState :=
      {| masterKey := None |}.

    Definition encryptBoxLoopPreBody
               (st : EncryptBoxState)
    : ebInput -> option ebOutput * EncryptBoxState
      := fun i =>
           match i with

             | ebSetMasterKey key
               => (if Algorithm.isValidMasterKey key as isValid return Algorithm.isValidMasterKey key = isValid -> _
                   then fun pf => (None,
                                   {| masterKey := Some (exist _ key pf) |})
                   else fun pf => (Some (inl (@ebErrorInvalidMasterKey key pf)),
                                   {| masterKey := None |})) eq_refl

             | ebSystemRandomness randomness (rawData, tag)
               => (match st.(masterKey) with
                     | None => Some (inl ebErrorNoMasterKey)
                     | Some (exist key pf)
                       => match Algorithm.encrypt randomness key pf rawData with
                            | inl enc
                              => Some (inr (ebEncrypted enc tag))
                            | inr (NotEnoughRandomness howMuchWanted randomnessGiven)
                              => Some (inl (ebErrorNotEnoughRandomness howMuchWanted randomnessGiven))
                          end
                   end,
                   st)

             | ebEncrypt rawData tag
               => let hint := Algorithm.randomnessHint rawData in
                  (Some (inr (ebRequestSystemRandomness hint (rawData, tag))), st)
           end.

    Definition encryptBoxLoopBody {T}
               (encryptBoxLoop : EncryptBoxState -> T)
               (st : EncryptBoxState)
    : ebInput -> action world * T
      := fun i => let outs := fst (encryptBoxLoopPreBody st i) in
                  (match outs with
                     | None => id
                     | Some out => handle out
                   end,
                   encryptBoxLoop (snd (encryptBoxLoopPreBody st i))).

    CoFixpoint encryptBoxLoop (st : EncryptBoxState) :=
      Step (encryptBoxLoopBody encryptBoxLoop st).

    Definition encryptBox : process _ _ := encryptBoxLoop initState.
  End trustedEncryptBox.
End TrustedEncryptBox.
