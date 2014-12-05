Set Implicit Arguments.

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
        let Y := if (i =? m - 1)%nat || (i =? m + n - 1)%nat then
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
    if (length IV =? 96)%nat then
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

Definition decrypt E K IV C A T :=
  let k := length T in
  let T' := Hash E K IV A k C in
  if T' =? T then
    let P := Encrypt E K IV C in
    Some P
  else
    None.
  