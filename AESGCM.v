Set Implicit Arguments.

Require Import AES.
Require Import GCM.
Require Import EncryptionInterface.

Module AESGCM <: EncryptionAlgorithm EncryptionStringDataTypes.

  Import EncryptionStringDataTypes.

  Require Import FPUtil.
  Require Import Arith NArith NPeano Ascii String List Bool.
  Import ListNotations.
  Local Open Scope prog_scope.
  Local Open Scope N_scope.
  Local Open Scope nat_scope.
  Local Open Scope string_scope.
  Local Open Scope list_scope.
  Local Open Scope bool_scope.
  Require Import Bitvec.
  Local Open Scope bitvec_scope.

  Local Notation bits := str_to_bitvec.
  Local Notation "# s" := (bits s) (at level 0).
  Local Notation str := bitvec_to_str.

  Infix "=?" := beq_nat : nat_scope.
  Infix "<>?" := bne_nat (at level 70) : nat_scope.

  (* a valid key is any string of length 16 (or 128 bit) *)
  Definition isValidMasterKey (key : masterKeyT) : bool := (String.length key =? 16)%nat.

  (* in unit of byte. Need 12 byte (or 96 bit) randomness *)
  Definition randomnessHint (rawData : rawDataT) : systemRandomnessHintT := 12.

  Definition encrypt (randomness : systemRandomnessT)
             (masterKey : masterKeyT)
             (masterKeyValid : isValidMasterKey masterKey = true)
             (rawData : rawDataT):
    encryptedDataT + EncryptionError systemRandomnessHintT systemRandomnessT :=
    let IV := #randomness in
    let IV_len := length IV in
    if  IV_len <? 96 then inr $ NotEnoughRandomness _ _ 96 randomness
    else
      let IV := firstn 96 IV in
      let (C, T) := GCM.encrypt AES.encrypt #masterKey IV #rawData [] 128 in
      inl $ str $ IV ++ T ++ C.

  Definition decrypt (masterKey : masterKeyT)
             (masterKeyValid : isValidMasterKey masterKey = true)
             (encryptedData : encryptedDataT) :
    rawDataT + DecryptionError :=
    let err := inr $ InvalidEncryptedData in
    let C := #encryptedData in
    if length C <? 96 + 128 then err
    else
      let (IV, C) := splitn 96 C in
      let (T, C) := splitn 128 C in
      match GCM.decrypt AES.encrypt #masterKey IV C [] T with
        | Some P => inl $ str $ P
        | None => err
      end.

  Lemma is_retraction : forall randomness masterKey masterKeyValid rawData,
                          let enc := encrypt randomness masterKey masterKeyValid rawData in
                          match enc with
                            | inl enc' => decrypt masterKey masterKeyValid enc' = inl rawData
                            | inr _ => True
                          end.
  Proof.
    admit.
  Qed.

  Definition doit (x : encryptedDataT + EncryptionError systemRandomnessHintT systemRandomnessT) :=
    match x with
      | inl s => s
      | _ => ""
    end.

  Definition check (x : rawDataT + DecryptionError) :=
    match x with
      | inl s => Some s
      | _ => None
    end.
  
  Arguments tl {A} _.
  Arguments removelast {A} _.

  Module test1.
    Definition K := "2kllajsf3jrl;kaj".
    Definition R := "9u8jg3q84-u8".
    Definition P := "8aIOw;fj8dfu[jqoir2wf[usjaiovu9r[2iojd0fawfs293jfE".
    Definition C := doit $ encrypt R K eq_refl P.
    Goal (check $ decrypt K eq_refl $ C) = Some P. r. Qed.
    Definition bad1 := list_to_str $ tl $ str_to_list $ C.
    Goal (check $ decrypt K eq_refl $ bad1) = None. r. Qed.
    Definition bad2 := list_to_str $ removelast $ str_to_list $ C.
    Goal (check $ decrypt K eq_refl $ bad2) = None. r. Qed.
    Definition replace3 := str_to_list "lajsfakls".
    Definition bad3 :=  list_to_str $ replace3 ++ skipn (length replace3) (str_to_list C).
    Goal (check $ decrypt K eq_refl $ bad3) = None. r. Qed.
  End test1.

  Module test2.
    Definition K := "9ap8usdjfaspd98f".
    Definition R := "as;jfafsioj;".
    Definition P := "".
    Definition C := doit $ encrypt R K eq_refl P.
    Goal (check $ decrypt K eq_refl $ C) = Some P. r. Qed.
    Definition bad1 := list_to_str $ tl $ str_to_list $ C.
    Goal (check $ decrypt K eq_refl $ bad1) = None. r. Qed.
    Definition bad2 := list_to_str $ removelast $ str_to_list $ C.
    Goal (check $ decrypt K eq_refl $ bad2) = None. r. Qed.
    Definition replace3 := str_to_list "lajsfakls".
    Definition bad3 :=  list_to_str $ replace3 ++ skipn (length replace3) (str_to_list C).
    Goal (check $ decrypt K eq_refl $ bad3) = None. r. Qed.
  End test2.

End AESGCM.