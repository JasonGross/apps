Set Implicit Arguments.

Require Import FPUtil.

Require Import AES.

Require Import Arith NArith NPeano Ascii String List.
Import ListNotations.
Open Scope N_scope.
Open Scope nat_scope.
Open Scope string_scope.
Open Scope list_scope.
Open Scope bitvec_scope.

Section GCM.

  Definition stateful_map S (upd : S -> S) (init : S) A (f : A -> S -> A) (ls : list A) : list A * S :=
    let step (p : list A * S) x :=
        let (acc, st) := p in
        let y := f x st in
        (y :: acc, upd st) in
    let (ls, final) := fold_left step ls ([], init) in
    (rev ls, final).

  Definition fold_left_i A B (f : nat -> A -> B -> A) (ls : list B) init init_i :=
    fst $ fold_left (fun (p : A * nat) x => let (a, i) := p in (f i a x, S i)) ls (init, init_i).

  Definition len A := @length A >> msb_of_nat 64.

  Infix "=?" := beq_nat : nat_scope.

  Definition gf128_mul := gf_mul 128 "11100001".

  Infix "*" := gf128_mul : bitvec_scope.
  Infix "+" := xor : bitvec_scope.

  Definition GHASH (H : b128) (A : bitvec) (C : bitvec) : b128 :=
    let As := slice 128 A in
    let Cs := slice 128 C in
    let m := length As in
    let n := length Cs in
    let step i (X Y : b128) :=
        let Y := if (i =? m - 1) || (i =? m + n - 1) then
                   right_trunc_pad_to 128 Y
                 else
                   Y in
        (X + Y) * H in
    let X := fold_left_i step (As ++ Cs) (zeros 128) 0 in
    (X + (len A ++ len C)) * H.

  Variable E : key_t -> b128 -> b128. 
  Variable K : key_t.
  Definition IV_t := bitvec.
  Variable IV : IV_t.
  Variable P : bitvec.
  Definition A_t := bitvec.
  Variable A : A_t.
  Variable t : nat.

  Definition H := E K $ zeros 128.

  Definition msb_unsign_plus (a b : bitvec) : bitvec := msb_of_N (length a) ((msb_to_N a) + (msb_to_N b))%N.

  Definition incr v := 
    let F_len := length v - 32 in
    let F := firstn F_len v in
    let I := skipn F_len v in
    F ++ (msb_unsign_plus I (msb_of_nat 32 1)).

  Definition Y0 : b128 :=
    if length IV =? 96 then
      IV ++ zeros 31 ++ bin "1"
    else
      GHASH H [] IV.

  Definition Encrypt : bitvec :=
    match P with
      | nil => nil
      | _ =>
        let Ps := slice 128 P in
        let Pi := removelast Ps in
        let Pn := last Ps (zeros 128) in
        let (Ci, Yn) := stateful_map incr (incr Y0) (fun Pi Yi => Pi + E K Yi) Pi in
        let Cn := Pn + firstn (length Pn) (E K Yn) in
        flat Ci ++ Cn
    end.

  Definition Hash := fun C => firstn t $ GHASH H A C + E K Y0.

End GCM.

Definition encrypt E K IV P A k := 
  let C := Encrypt E K IV P in
  let T := Hash E K IV A k C in
  (C, T).

Fixpoint forall2 A B (p : A -> B -> bool) ls1 ls2 :=
  match ls1, ls2 with
    | a :: ls1, b :: ls2 => p a b && forall2 p ls1 ls2
    | nil, nil => true
    | _, _ => false
  end.

Definition bitvec_eqb := forall2 Bool.eqb.
Infix "=?" := bitvec_eqb : bitvec_scope.
Goal bin "101" =? bin "101" = true. r. Qed.
Goal bin "101" =? bin "10" = false. r. Qed.
Goal hex "ab" =? hex "ab" = true. r. Qed.
Goal hex "ab" =? hex "ac" = false. r. Qed.

Definition decrypt E K IV C A T :=
  let k := length T in
  let T' := Hash E K IV A k C in
  if T' =? T then
    let P := Encrypt E K IV C in
    Some P
  else
    None.
  
Notation E := AES.encrypt.

Module test1.
  Definition t_K := hex "00000000000000000000000000000000".
  Definition t_P := hex "".
  Definition t_IV := hex "000000000000000000000000".
  Definition t_H := hex "66e94bd4ef8a2c3b884cfa59ca342b2e".
  Goal (H E t_K) = t_H. r. Qed.
  Definition t_Y0 := hex "00000000000000000000000000000001".
  Goal (Y0 E t_K t_IV) = t_Y0. r. Qed.
  Definition t_E_K_Y0 := hex "58e2fccefa7e3061367f1d57a4e7455a".
  Goal E t_K t_Y0 = t_E_K_Y0. r. Qed.
  Definition t_C := hex "".
  Goal (Encrypt E t_K t_IV t_P) = t_C. r. Qed.
  Definition t_lenA_lenC := hex "00000000000000000000000000000000".
  Definition t_A := hex "".
  Goal len t_A ++ len t_C = t_lenA_lenC. r. Qed.
  Definition t_GHASH := hex "00000000000000000000000000000000".
  Goal GHASH t_H t_A t_C = t_GHASH. r. Qed.
  Definition t_T := hex "58e2fccefa7e3061367f1d57a4e7455a".
  Definition t_t := 128.
  Goal encrypt E t_K t_IV t_P t_A t_t = (t_C, t_T). r. Qed.
  Goal (decrypt E t_K t_IV t_C t_A t_T) = Some t_P. r. Qed.
End test1.

Module test2.
  Definition t_K := hex "00000000000000000000000000000000".
  Definition t_P := hex "00000000000000000000000000000000".
  Definition t_IV := hex "000000000000000000000000".
  Definition t_H := hex "66e94bd4ef8a2c3b884cfa59ca342b2e".
  Goal (H E t_K) = t_H. r. Qed.
  Definition t_Y0 := hex "00000000000000000000000000000001".
  Goal (Y0 E t_K t_IV) = t_Y0. r. Qed.
  Definition t_E_K_Y0 := hex "58e2fccefa7e3061367f1d57a4e7455a".
  Goal E t_K t_Y0 = t_E_K_Y0. r. Qed.
  Definition t_C := hex "0388dace60b6a392f328c2b971b2fe78".
  Goal (Encrypt E t_K t_IV t_P) = t_C. r. Qed.
  Definition t_lenA_lenC := hex "00000000000000000000000000000080".
  Definition t_A := hex "".
  Goal len t_A ++ len t_C = t_lenA_lenC. r. Qed.
  Definition t_GHASH := hex "f38cbb1ad69223dcc3457ae5b6b0f885".
  Goal GHASH t_H t_A t_C = t_GHASH. r. Qed.
  Definition t_T := hex "ab6e47d42cec13bdf53a67b21257bddf".
  Definition t_t := 128.
  Goal encrypt E t_K t_IV t_P t_A t_t = (t_C, t_T). r. Qed.
  Goal (decrypt E t_K t_IV t_C t_A t_T) = Some t_P. r. Qed.
  Definition noise := left_trunc_pad_to (length t_C) $ hex "000001000".
  Goal (decrypt E t_K t_IV (t_C + noise) t_A t_T) = None. r. Qed.
End test2.

Module test3.
  Definition t_K := hex "feffe9928665731c6d6a8f9467308308".
  Definition t_P := flat $ map hex ["d9313225f88406e5a55909c5aff5269a";
                                     "86a7a9531534f7da2e4c303d8a318a72";
                                     "1c3c0c95956809532fcf0e2449a6b525";
                                     "b16aedf5aa0de657ba637b391aafd255"].
  Definition t_IV := hex "cafebabefacedbaddecaf888".
  Definition t_H := hex "b83b533708bf535d0aa6e52980d53b78".
  Goal (H E t_K) = t_H. r. Qed.
  Definition t_Y0 := hex "cafebabefacedbaddecaf88800000001".
  Goal (Y0 E t_K t_IV) = t_Y0. r. Qed.
  Definition t_E_K_Y0 := hex "3247184b3c4f69a44dbcd22887bbb418".
  Goal E t_K t_Y0 = t_E_K_Y0. r. Qed.
  Definition t_C := flat $ map hex ["42831ec2217774244b7221b784d0d49c";
                                     "e3aa212f2c02a4e035c17e2329aca12e";
                                     "21d514b25466931c7d8f6a5aac84aa05";
                                     "1ba30b396a0aac973d58e091473f5985"].
  Goal (Encrypt E t_K t_IV t_P) = t_C. r. Qed.
  Definition t_lenA_lenC := hex "00000000000000000000000000000200".
  Definition t_A := hex "".
  Goal len t_A ++ len t_C = t_lenA_lenC. r. Qed.
  Definition t_GHASH := hex "7f1b32b81b820d02614f8895ac1d4eac".
  Goal GHASH t_H t_A t_C = t_GHASH. r. Qed.
  Definition t_T := hex "4d5c2af327cd64a62cf35abd2ba6fab4".
  Definition t_t := 128.
  Goal encrypt E t_K t_IV t_P t_A t_t = (t_C, t_T). r. Qed.
  Goal (decrypt E t_K t_IV t_C t_A t_T) = Some t_P. r. Qed.
  Definition noise := left_trunc_pad_to (length t_C) $ hex "000001000".
  Goal (decrypt E t_K t_IV (t_C + noise) t_A t_T) = None. r. Qed.
End test3.

Module test4.
  Definition t_K := hex "feffe9928665731c6d6a8f9467308308".
  Definition t_P := flat $ map hex ["d9313225f88406e5a55909c5aff5269a";
                                     "86a7a9531534f7da2e4c303d8a318a72";
                                     "1c3c0c95956809532fcf0e2449a6b525";
                                     "b16aedf5aa0de657ba637b39"].
  Definition t_A := flat $ map hex ["feedfacedeadbeeffeedfacedeadbeef";
                                     "abaddad2"].
  Definition t_IV := hex "cafebabefacedbaddecaf888".
  Definition t_H := hex "b83b533708bf535d0aa6e52980d53b78".
  Goal (H E t_K) = t_H. r. Qed.
  Definition t_Y0 := hex "cafebabefacedbaddecaf88800000001".
  Goal (Y0 E t_K t_IV) = t_Y0. r. Qed.
  Definition t_E_K_Y0 := hex "3247184b3c4f69a44dbcd22887bbb418".
  Goal E t_K t_Y0 = t_E_K_Y0. r. Qed.
  Definition t_C := flat $ map hex ["42831ec2217774244b7221b784d0d49c";
                                     "e3aa212f2c02a4e035c17e2329aca12e";
                                     "21d514b25466931c7d8f6a5aac84aa05";
                                     "1ba30b396a0aac973d58e091"].
  Goal (Encrypt E t_K t_IV t_P) = t_C. r. Qed.
  Definition t_lenA_lenC := hex "00000000000000a000000000000001e0".
  Goal len t_A ++ len t_C = t_lenA_lenC. r. Qed.
  Definition t_GHASH := hex "698e57f70e6ecc7fd9463b7260a9ae5f".
  Goal GHASH t_H t_A t_C = t_GHASH. r. Qed.
  Definition t_T := hex "5bc94fbc3221a5db94fae95ae7121a47".
  Definition t_t := 128.
  Goal encrypt E t_K t_IV t_P t_A t_t = (t_C, t_T). r. Qed.
  Goal (decrypt E t_K t_IV t_C t_A t_T) = Some t_P. r. Qed.
  Definition noise := left_trunc_pad_to (length t_C) $ hex "000001000".
  Goal (decrypt E t_K t_IV (t_C + noise) t_A t_T) = None. r. Qed.
End test4.

Module test5.
  Definition t_K := hex "feffe9928665731c6d6a8f9467308308".
  Definition t_P := flat $ map hex ["d9313225f88406e5a55909c5aff5269a";
                                     "86a7a9531534f7da2e4c303d8a318a72";
                                     "1c3c0c95956809532fcf0e2449a6b525";
                                     "b16aedf5aa0de657ba637b39"].
  Definition t_A := flat $ map hex ["feedfacedeadbeeffeedfacedeadbeef";
                                     "abaddad2"].
  Definition t_IV := hex "cafebabefacedbad".
  Definition t_H := hex "b83b533708bf535d0aa6e52980d53b78".
  Goal (H E t_K) = t_H. r. Qed.
  Definition t_Y0 := hex "c43a83c4c4badec4354ca984db252f7d".
  Goal (Y0 E t_K t_IV) = t_Y0. r. Qed.
  Definition t_E_K_Y0 := hex "e94ab9535c72bea9e089c93d48e62fb0".
  Goal E t_K t_Y0 = t_E_K_Y0. r. Qed.
  Definition t_C := flat $ map hex ["61353b4c2806934a777ff51fa22a4755";
                                     "699b2a714fcdc6f83766e5f97b6c7423";
                                     "73806900e49f24b22b097544d4896b42";
                                     "4989b5e1ebac0f07c23f4598"].
  Goal (Encrypt E t_K t_IV t_P) = t_C. r. Qed.
  Definition t_lenA_lenC := hex "00000000000000a000000000000001e0".
  Goal len t_A ++ len t_C = t_lenA_lenC. r. Qed.
  Definition t_GHASH := hex "df586bb4c249b92cb6922877e444d37b".
  Goal GHASH t_H t_A t_C = t_GHASH. r. Qed.
  Definition t_T := hex "3612d2e79e3b0785561be14aaca2fccb".
  Definition t_t := 128.
  Goal encrypt E t_K t_IV t_P t_A t_t = (t_C, t_T). r. Qed.
  Goal (decrypt E t_K t_IV t_C t_A t_T) = Some t_P. r. Qed.
  Definition noise := left_trunc_pad_to (length t_C) $ hex "000001000".
  Goal (decrypt E t_K t_IV (t_C + noise) t_A t_T) = None. r. Qed.
End test5.

Module test6.
  Definition t_K := hex "feffe9928665731c6d6a8f9467308308".
  Definition t_P := flat $ map hex ["d9313225f88406e5a55909c5aff5269a";
                                     "86a7a9531534f7da2e4c303d8a318a72";
                                     "1c3c0c95956809532fcf0e2449a6b525";
                                     "b16aedf5aa0de657ba637b39"].
  Definition t_A := flat $ map hex ["feedfacedeadbeeffeedfacedeadbeef";
                                     "abaddad2"].
  Definition t_IV := flat $ map hex ["9313225df88406e555909c5aff5269aa";
                                      "6a7a9538534f7da1e4c303d2a318a728";
                                      "c3c0c95156809539fcf0e2429a6b5254";
                                      "16aedbf5a0de6a57a637b39b"].
  Definition t_H := hex "b83b533708bf535d0aa6e52980d53b78".
  Goal (H E t_K) = t_H. r. Qed.
  Definition t_Y0 := hex "3bab75780a31c059f83d2a44752f9864".
  Goal (Y0 E t_K t_IV) = t_Y0. r. Qed.
  Definition t_E_K_Y0 := hex "7dc63b399f2d98d57ab073b6baa4138e".
  Goal E t_K t_Y0 = t_E_K_Y0. r. Qed.
  Definition t_C := flat $ map hex ["8ce24998625615b603a033aca13fb894";
                                     "be9112a5c3a211a8ba262a3cca7e2ca7";
                                     "01e4a9a4fba43c90ccdcb281d48c7c6f";
                                     "d62875d2aca417034c34aee5"].
  Goal (Encrypt E t_K t_IV t_P) = t_C. r. Qed.
  Definition t_lenA_lenC := hex "00000000000000a000000000000001e0".
  Goal len t_A ++ len t_C = t_lenA_lenC. r. Qed.
  Definition t_GHASH := hex "1c5afe9760d3932f3c9a878aac3dc3de".
  Goal GHASH t_H t_A t_C = t_GHASH. r. Qed.
  Definition t_T := hex "619cc5aefffe0bfa462af43c1699d050".
  Definition t_t := 128.
  Goal encrypt E t_K t_IV t_P t_A t_t = (t_C, t_T). r. Qed.
  Goal (decrypt E t_K t_IV t_C t_A t_T) = Some t_P. r. Qed.
  Definition noise := left_trunc_pad_to (length t_C) $ hex "000001000".
  Goal (decrypt E t_K t_IV (t_C + noise) t_A t_T) = None. r. Qed.
End test6.
