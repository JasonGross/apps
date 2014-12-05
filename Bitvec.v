(* bit vectors. Not length-indexed *)

Set Implicit Arguments.

Require Import FPUtil.

Require Import Arith NArith NPeano Ascii String List.
Import ListNotations.
Local Open Scope prog_scope.
Local Open Scope N_scope.
Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition bitvec := list bool.

Definition b128 := bitvec.

Definition b352 := bitvec.

Definition b32 := bitvec.

Definition byte := bitvec.

Definition get_slice A (vec : list A) begin len := firstn len (skipn begin vec).

Definition get (width : nat) (vec : bitvec) (idx : nat) := get_slice vec (width * idx) width.

Definition set_slice A (vec : list A) begin value := firstn begin vec ++ value ++ skipn (begin + length value) vec.

Definition set (width : nat) (vec : bitvec) (idx : nat) value := set_slice vec (width * idx) value.

Definition key_t := b128.

Definition key_schedule_t := b352.

Definition zeros := repeat false.

Definition of_bin_ascii (ch : ascii) :=
  (match ch with
     | "0" => false
     | _ => true
   end)%char.

Definition bitvec_of_bin_str : string -> bitvec := map of_bin_ascii << str_to_list.
Coercion bitvec_of_bin_str : string >-> bitvec.
Notation bin := bitvec_of_bin_str.

Notation t := true.
Notation f := false.

(* trunc or padding zeros on the right *)
Definition right_trunc_pad_to len (vec : bitvec) : bitvec := firstn len vec ++ zeros (len - length vec).

(* convert positive to LSB-first bitvec *)
Fixpoint lsb_of_pos (p : positive) : bitvec :=
  match p with
    | xH => [true]
    | xI p => true :: lsb_of_pos p
    | xO p => false :: lsb_of_pos p
  end.

Definition lsb_of_N (n : N) : byte := 
  match n with
    | N0 => [false]
    | Npos p => lsb_of_pos p
  end.

Fixpoint lsb_to_N (vec : bitvec) : N :=
  match vec with
    | nil => N0
    | b :: vec =>
      match lsb_to_N vec with
        | N0 => if b then Npos xH else N0
        | Npos p => 
          let p := if b then xI p else xO p in 
          Npos p
      end
  end.

Definition lsb_to_nat : bitvec -> nat := lsb_to_N >> nat_of_N.

Goal lsb_to_nat "1100" = 3. r. Qed.
Goal lsb_to_nat "1101" = 11. r. Qed.

(* byte is in MSB-first format *)

Arguments rev {A} _.

Definition msb_to_N := rev >> lsb_to_N.
Definition msb_to_nat := rev >> lsb_to_nat.

(* convert N to MSB-first bitvec *)
Definition msb_of_N (width : nat) (n : N) : bitvec := 
  rev $ right_trunc_pad_to width (lsb_of_N n).

Definition msb_of_nat (width : nat) (n : nat) : bitvec := msb_of_N width (N.of_nat n).

Definition byte_of_N (n : N) : byte := msb_of_N 8 n.

Definition byte_of_nat (n : nat) : byte := msb_of_nat 8 n.
Coercion byte_of_nat : nat >-> byte.

Goal byte_of_nat 3 = "00000011" :> bitvec. r. Qed.

Definition byte_to_nat (b : byte) : nat := msb_to_nat b.

Definition N_of_hex_ascii (ch : ascii) : N := default 0%N $ msum $ map (fun x : ascii * ascii * N => let (p, base) := x in N_of_ascii_in (fst p) (snd p) base ch) [("0", "9", 0%N); ("A", "F", 10%N); ("a", "f", 10%N)]%char.

Definition map_byte (f : byte -> byte) (vec : bitvec) : bitvec := map_every 8 f vec.

(* hex string is in bytewise-MSB-first format *)
Definition halfbyte_of_hex_ascii := rev << right_trunc_pad_to 4 << lsb_of_N << N_of_hex_ascii.

Definition remove_space (ch : ascii) :=
  match ch with
    | " "%char => false
    | _ => true
  end.

Definition bitvec_of_hex : string -> bitvec := flat << map halfbyte_of_hex_ascii << filter remove_space << str_to_list.

Definition left_trunc_pad_to n := rev << right_trunc_pad_to n << rev.

Definition byte_of_hex : string -> byte := left_trunc_pad_to 8 << bitvec_of_hex.

Definition halfbyte_to_hex (v : bitvec) : ascii :=
  let n := lsb_to_nat (rev v) in
  let n0 := nat_of_ascii "0" in
  let nA := nat_of_ascii "A" in
  if n <? 10 then
    ascii_of_nat (n0 + n)
  else
    ascii_of_nat (nA + n - 10).

Goal halfbyte_to_hex "1011" = "B"%char. r. Qed.

Definition bitvec_to_hex := list_to_str << map halfbyte_to_hex << slice 4.

Notation hex := bitvec_of_hex.
Notation show := bitvec_to_hex.

Definition bitvec_eqb := forall2 Bool.eqb.
Infix "=?" := bitvec_eqb : bitvec_scope.
Local Open Scope bitvec_scope.

Goal bin "101" =? bin "101" = true. r. Qed.
Goal bin "101" =? bin "10" = false. r. Qed.
Goal hex "ab" =? hex "ab" = true. r. Qed.
Goal hex "ab" =? hex "ac" = false. r. Qed.

Definition bit_xor (a b : bool) : bool :=
  match a, b with
    | true, false => true
    | false, true => true
    | _, _ => false
  end.

Definition xor (a b : bitvec) : bitvec := map2 bit_xor a b.

Definition rshift n (v : bitvec) := zeros n ++ firstn (length v - n) v.

Arguments fst {A B} _.
Arguments fold_left {A B} _ _ _.

Definition f231 A B C D (f : A -> B -> C -> D) b c a := f a b c.

Infix "+" := xor : bitvec_scope.

Definition gf_mul n R (a b : bitvec) : bitvec :=
  let R := right_trunc_pad_to n R in
  fst $ f231 fold_left b (zeros n, a) (fun st bi =>
    let (Z, V) := st in
    let Z := if bi then
               Z + V
             else
               Z in
    let V := if nth (n - 1) V false then
               rshift 1 V + R
             else
               rshift 1 V in
    (Z, V)).
