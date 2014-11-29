Require Import Coq.Strings.String.

Module Type EncryptionDataTypes.
  (** Type of unencrypted data *)
  Parameter rawDataT : Type.
  (** Type of the master key used for encryption *)
  Parameter masterKeyT : Type.
  (** Type of the encrypted data *)
  Parameter encryptedDataT : Type.
  (** Type of the randomness used for the algorithm. *)
  Parameter systemRandomnessT : Type.

  (** Type of a hint to give the system about how much randomness is
      desired (e.g., number of bytes).  No guarantees are made about
      the amount of randomness acquired. *)
  Parameter systemRandomnessHintT : Type.
End EncryptionDataTypes.

Module EncryptionStringDataTypes <: EncryptionDataTypes.
  Definition rawDataT := string.
  Definition masterKeyT := string.
  Definition encryptedDataT := string.
  Definition systemRandomnessT := string.
  Definition systemRandomnessHintT := nat.
End EncryptionStringDataTypes.

Inductive EncryptionError systemRandomnessHintT systemRandomnessT :=
| NotEnoughRandomness (howMuchWanted : systemRandomnessHintT) (randomnessGiven : systemRandomnessT).

Inductive DecryptionError :=
| InvalidEncryptedData.

Module Type EncryptionAlgorithm (DataTypes : EncryptionDataTypes).
  Import DataTypes.

  Parameter isValidMasterKey : masterKeyT -> bool.

  Parameter randomnessHint : forall (rawData : rawDataT),
                               systemRandomnessHintT.

  Parameter encrypt : forall (randomness : systemRandomnessT)
                             (masterKey : masterKeyT)
                             (masterKeyValid : isValidMasterKey masterKey = true)
                             (rawData : rawDataT),
                        encryptedDataT + EncryptionError systemRandomnessHintT systemRandomnessT.

  Parameter decrypt : forall (masterKey : masterKeyT)
                             (masterKeyValid : isValidMasterKey masterKey = true)
                             (encryptedData : encryptedDataT),
                        rawDataT + DecryptionError.

  Axiom is_retraction : forall randomness masterKey masterKeyValid rawData,
                          let enc := encrypt randomness masterKey masterKeyValid rawData in
                          match enc with
                            | inl enc' => decrypt masterKey masterKeyValid enc' = inl rawData
                            | inr _ => True
                          end.
End EncryptionAlgorithm.
