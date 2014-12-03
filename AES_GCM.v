Set Implicit Arguments.

Module Util.

  Require Import String.
  Open Scope string_scope.
  Require Import List.
  Import ListNotations.
  Open Scope list_scope.

  (* functional programming utilities *)

  Require Import Program.Basics.

  Infix "@" := compose (at level 40) : prog_scope.
  Infix ">>" := (flip compose) (at level 40) : prog_scope.

  Definition apply {A B} (f : A -> B) x := f x.
  Infix "$" := apply (at level 85, right associativity) : prog_scope.

  Definition flip A B C (f : A -> B -> C) b a := f a b.

  Open Scope prog_scope.

  (* option utilities *)

  Fixpoint msum {A} (ls : list (option A)) : option A :=
    match ls with
      | Some a :: _ => Some a
      | None :: ls => msum ls
      | nil => None
    end.

  Definition default A def (o : option A) : A :=
    match o with
      | Some a => a
      | None => def
    end.

  Require Import Ascii.
  Require Import Bool.
  Open Scope bool_scope.
  Require Import NArith.
  Open Scope N_scope.
  Open Scope nat_scope.

  (* list utilities *)

  Definition flat {A} (ls : list (list A)) := flat_map id ls.

  Definition sum A (zero : A) (add : A -> A -> A) (ls : list A) : A := fold_left add ls zero.
    
  Fixpoint repeat A (a : A) n :=
    match n with
      | 0 => nil
      | S n => a :: repeat a n
    end.

  Definition lcshift A n (ls : list A) := skipn n ls ++ firstn n ls.

  Fixpoint prependToAll A (sep : A) ls :=
    match ls with
      | nil => nil
      | x :: xs => sep :: x :: prependToAll sep xs
    end.

  Definition intersperse A (sep : A) ls :=
    match ls with
      | nil => nil
      | x :: xs => x :: prependToAll sep xs
    end.

  Fixpoint map2 A B C (f : A -> B -> C) ls1 ls2 :=
    match ls1, ls2 with
      | a :: ls1, b :: ls2 => f a b :: map2 f ls1 ls2
      | _, _ => nil
    end.

  Fixpoint mapi' base {A B} (f : nat -> A -> B) (ls : list A) : list B :=
    match ls with
      | x :: xs => f base x :: mapi' (S base) f xs
      | nil => nil
    end.

  Definition mapi {A B} := @mapi' 0 A B.

  (* a specialize version of fold_left for [begin,begin+1,...,begin+len-1] *)
  Fixpoint iter_range A (f : A -> nat -> A) begin len init :=
    match len with
      | 0 => init
      | S n' => iter_range f (S begin) n' (f init begin)
    end.

  Definition iter A f := @iter_range A f 0.

  (* f (...) (begin+len-1) :: ... :: f (f init begin) (begin+1) :: f init begin :: init_res *)
  Definition iter_range_collect_rev A (f : A -> nat -> A) begin len init init_res: list A :=
    snd (iter_range 
           (fun p n => 
              let old := fst p in 
              let ls := snd p in 
              let new := f old n in
              (new, new :: ls))
           begin len (init, init_res)).

  Definition iter_range_collect A f begin len (init : A) init_res := rev (iter_range_collect_rev f begin len init (rev init_res)).

  Definition iter_collect A f n := @iter_range_collect A f 0 n .

  (* a special version of map for [begin; begin+1; ...; begin+len-1] *)
  Fixpoint for_range A begin len (f : nat -> A) :=
    match len with
      | 0 => []
      | S n => f begin :: for_range (S begin) n f
    end.

  Definition for_n A len := @for_range A 0 len.

  (* slicing *)
  Fixpoint slice' (count : nat) A (width : nat) (ls : list A) : list (list A) :=
    match count with
      | 0 => nil
      | S count => firstn width ls :: slice' count width (skipn width ls)
    end.

  Require Import NPeano.

  Definition slice A (width : nat) (ls : list A) : list (list A) :=
    slice' (length ls / width) width ls.

  Definition mapi_every A (width : nat) (f : nat -> list A -> list A) (ls : list A) : list A :=
    flat (mapi f (slice width ls)).

  Definition map_every A n f := @mapi_every A n (fun _ e => f e).

  (* string/ascii utilities *)
  
  (* if ch in in range [a, b], return (Some (ch - a + base)) *)
  Definition N_of_ascii_in (a b : ascii) (base : N) (ch: ascii) : option N :=
    (let asc := N_of_ascii ch in
     let ascA := N_of_ascii a in
     let ascB := N_of_ascii b in
     if (ascA <=? asc) && (asc <=? ascB) then
       Some (asc - ascA + base)
     else
       None
    )%N.

  Fixpoint str_to_list (str : string) :=
    match str with
      | String c s => c :: str_to_list s
      | _ => nil
    end.

  Fixpoint list_to_str ls : string :=
    match ls with
      | c :: ls => String c (list_to_str ls)
      | nil => EmptyString
    end.

  Definition intersperse_every n sep := str_to_list >> slice n >> intersperse (str_to_list sep) >> flat >> list_to_str.

End Util.

Import Util.

(* AES with 128-bit key *)

Section AES.

  Require Import Arith NArith NPeano Ascii String List.
  Import ListNotations.
  Open Scope N.
  Open Scope nat.
  Open Scope string.
  Open Scope list.

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

  Variable key : key_t.

  Definition key_schedule_t := b352.

  Definition zeros := repeat false.

  Definition of_bin_ascii (ch : ascii) :=
    (match ch with
       | "0" => false
       | _ => true
     end)%char.

  Definition bitvec_of_bin_str : string -> bitvec := map of_bin_ascii @ str_to_list.

  Coercion bitvec_of_bin_str : string >-> bitvec.

  Notation t := true.
  Notation f := false.

  (* bitvec is in LSB-first format *)

  Definition trunc_pad_to len (vec : bitvec) : bitvec := firstn len vec ++ zeros (len - length vec).

  Fixpoint bitvec_of_pos (p : positive) : bitvec :=
    match p with
      | xH => [true]
      | xI p => true :: bitvec_of_pos p
      | xO p => false :: bitvec_of_pos p
    end.

  Definition bitvec_of_N (n : N) : byte := 
    match n with
      | N0 => [false]
      | Npos p => bitvec_of_pos p
    end.

  Fixpoint bitvec_to_nat (vec : bitvec) : nat := 
    match vec with
      | nil => 0
      | b :: vec => (if b then 1 else 0) + 2 * bitvec_to_nat vec
    end.

  Goal bitvec_to_nat "1100" = 3. reflexivity. Qed.

  (* byte is in MSB-first format *)

  Arguments rev {A} _.

  Definition byte_of_N (n : N) : byte := 
    rev $ trunc_pad_to 8 (bitvec_of_N n).

  Definition byte_of_nat (n : nat) : byte := byte_of_N (N.of_nat n).
  Coercion byte_of_nat : nat >-> byte.
  
  Goal byte_of_nat 3 = "00000011" :> bitvec. reflexivity. Qed.

  Definition byte_to_nat (b : byte) : nat := bitvec_to_nat $ rev b.

  Definition N_of_hex_ascii (ch : ascii) : N := default 0%N $ msum $ map (fun x : ascii * ascii * N => let (p, base) := x in N_of_ascii_in (fst p) (snd p) base ch) [("0", "9", 0%N); ("A", "F", 10%N); ("a", "f", 10%N)]%char.

  Definition map_byte (f : byte -> byte) (vec : bitvec) : bitvec := map_every 8 f vec.

  (* hex string is in bytewise-MSB-first format *)
  Definition halfbyte_of_hex_ascii := rev @ trunc_pad_to 4 @ bitvec_of_N @ N_of_hex_ascii.

  Definition remove_space (ch : ascii) :=
    match ch with
      | " "%char => false
      | _ => true
    end.

  Definition bitvec_of_hex : string -> bitvec := flat @ map halfbyte_of_hex_ascii @ filter remove_space @ str_to_list.

  Definition left_trunc_pad_to n := rev @ trunc_pad_to n @ rev.

  Definition byte_of_hex : string -> byte := left_trunc_pad_to 8 @ bitvec_of_hex.

  Definition halfbyte_to_hex (v : bitvec) : ascii :=
    let n := bitvec_to_nat (rev v) in
    let n0 := nat_of_ascii "0" in
    let nA := nat_of_ascii "A" in
    if n <? 10 then
      ascii_of_nat (n0 + n)
    else
      ascii_of_nat (nA + n - 10).

  Goal halfbyte_to_hex "1011" = "B"%char. reflexivity. Qed.

  Definition bitvec_to_hex := list_to_str @ map halfbyte_to_hex @ slice 4.

  Definition s_box : list byte := map byte_of_hex
  [
    "63"; "7C"; "77"; "7B"; "F2"; "6B"; "6F"; "C5"; "30"; "01"; "67"; "2B"; "FE"; "D7"; "AB"; "76";
    "CA"; "82"; "C9"; "7D"; "FA"; "59"; "47"; "F0"; "AD"; "D4"; "A2"; "AF"; "9C"; "A4"; "72"; "C0";
    "B7"; "FD"; "93"; "26"; "36"; "3F"; "F7"; "CC"; "34"; "A5"; "E5"; "F1"; "71"; "D8"; "31"; "15";
    "04"; "C7"; "23"; "C3"; "18"; "96"; "05"; "9A"; "07"; "12"; "80"; "E2"; "EB"; "27"; "B2"; "75";
    "09"; "83"; "2C"; "1A"; "1B"; "6E"; "5A"; "A0"; "52"; "3B"; "D6"; "B3"; "29"; "E3"; "2F"; "84";
    "53"; "D1"; "00"; "ED"; "20"; "FC"; "B1"; "5B"; "6A"; "CB"; "BE"; "39"; "4A"; "4C"; "58"; "CF";
    "D0"; "EF"; "AA"; "FB"; "43"; "4D"; "33"; "85"; "45"; "F9"; "02"; "7F"; "50"; "3C"; "9F"; "A8";
    "51"; "A3"; "40"; "8F"; "92"; "9D"; "38"; "F5"; "BC"; "B6"; "DA"; "21"; "10"; "FF"; "F3"; "D2";
    "CD"; "0C"; "13"; "EC"; "5F"; "97"; "44"; "17"; "C4"; "A7"; "7E"; "3D"; "64"; "5D"; "19"; "73";
    "60"; "81"; "4F"; "DC"; "22"; "2A"; "90"; "88"; "46"; "EE"; "B8"; "14"; "DE"; "5E"; "0B"; "DB";
    "E0"; "32"; "3A"; "0A"; "49"; "06"; "24"; "5C"; "C2"; "D3"; "AC"; "62"; "91"; "95"; "E4"; "79";
    "E7"; "C8"; "37"; "6D"; "8D"; "D5"; "4E"; "A9"; "6C"; "56"; "F4"; "EA"; "65"; "7A"; "AE"; "08";
    "BA"; "78"; "25"; "2E"; "1C"; "A6"; "B4"; "C6"; "E8"; "DD"; "74"; "1F"; "4B"; "BD"; "8B"; "8A";
    "70"; "3E"; "B5"; "66"; "48"; "03"; "F6"; "0E"; "61"; "35"; "57"; "B9"; "86"; "C1"; "1D"; "9E";
    "E1"; "F8"; "98"; "11"; "69"; "D9"; "8E"; "94"; "9B"; "1E"; "87"; "E9"; "CE"; "55"; "28"; "DF";
    "8C"; "A1"; "89"; "0D"; "BF"; "E6"; "42"; "68"; "41"; "99"; "2D"; "0F"; "B0"; "54"; "BB"; "16"
  ].

  Goal nth 1 s_box 0 = "01111100" :> bitvec. reflexivity. Qed.
  Goal nth 16 s_box 0 = "11001010" :> bitvec. reflexivity. Qed.
  Goal bitvec_to_hex (nth 1 s_box 0) = "7C". reflexivity. Qed.
  Goal bitvec_to_hex (nth 16 s_box 0) = "CA". reflexivity. Qed.
  
  Definition inv_s_box : list byte := map byte_of_hex
  [
    "52"; "09"; "6A"; "D5"; "30"; "36"; "A5"; "38"; "BF"; "40"; "A3"; "9E"; "81"; "F3"; "D7"; "FB";
    "7C"; "E3"; "39"; "82"; "9B"; "2F"; "FF"; "87"; "34"; "8E"; "43"; "44"; "C4"; "DE"; "E9"; "CB";
    "54"; "7B"; "94"; "32"; "A6"; "C2"; "23"; "3D"; "EE"; "4C"; "95"; "0B"; "42"; "FA"; "C3"; "4E";
    "08"; "2E"; "A1"; "66"; "28"; "D9"; "24"; "B2"; "76"; "5B"; "A2"; "49"; "6D"; "8B"; "D1"; "25";
    "72"; "F8"; "F6"; "64"; "86"; "68"; "98"; "16"; "D4"; "A4"; "5C"; "CC"; "5D"; "65"; "B6"; "92";
    "6C"; "70"; "48"; "50"; "FD"; "ED"; "B9"; "DA"; "5E"; "15"; "46"; "57"; "A7"; "8D"; "9D"; "84";
    "90"; "D8"; "AB"; "00"; "8C"; "BC"; "D3"; "0A"; "F7"; "E4"; "58"; "05"; "B8"; "B3"; "45"; "06";
    "D0"; "2C"; "1E"; "8F"; "CA"; "3F"; "0F"; "02"; "C1"; "AF"; "BD"; "03"; "01"; "13"; "8A"; "6B";
    "3A"; "91"; "11"; "41"; "4F"; "67"; "DC"; "EA"; "97"; "F2"; "CF"; "CE"; "F0"; "B4"; "E6"; "73";
    "96"; "AC"; "74"; "22"; "E7"; "AD"; "35"; "85"; "E2"; "F9"; "37"; "E8"; "1C"; "75"; "DF"; "6E";
    "47"; "F1"; "1A"; "71"; "1D"; "29"; "C5"; "89"; "6F"; "B7"; "62"; "0E"; "AA"; "18"; "BE"; "1B";
    "FC"; "56"; "3E"; "4B"; "C6"; "D2"; "79"; "20"; "9A"; "DB"; "C0"; "FE"; "78"; "CD"; "5A"; "F4";
    "1F"; "DD"; "A8"; "33"; "88"; "07"; "C7"; "31"; "B1"; "12"; "10"; "59"; "27"; "80"; "EC"; "5F";
    "60"; "51"; "7F"; "A9"; "19"; "B5"; "4A"; "0D"; "2D"; "E5"; "7A"; "9F"; "93"; "C9"; "9C"; "EF";
    "A0"; "E0"; "3B"; "4D"; "AE"; "2A"; "F5"; "B0"; "C8"; "EB"; "BB"; "3C"; "83"; "53"; "99"; "61";
    "17"; "2B"; "04"; "7E"; "BA"; "77"; "D6"; "26"; "E1"; "69"; "14"; "63"; "55"; "21"; "0C"; "7D"
  ].

  Definition RC : list byte := map byte_of_hex
  [ 
    "01"; "02"; "04"; "08"; "10"; "20"; "40"; "80"; "1b"; "36" 
  ].

  Definition list_get (ls : list byte) idx := nth idx ls 0.

  Definition sub_byte (b : byte) := list_get s_box (byte_to_nat b).

  Definition sub_bytes := map sub_byte.

  Definition get_byte := get 8.
  Definition set_byte := set 8.

  Definition lcshift_byte := @lcshift bool 8.

  Definition bit_xor (a b : bool) : bool :=
    match a, b with
      | true, false => true
      | false, true => true
      | _, _ => false
    end.

  Definition xor (a b : bitvec) : bitvec := map2 bit_xor a b.

  Infix "+" := xor : bitvec_scope.
  Open Scope bitvec_scope.

  Definition g n (w : key_t) :=
    let w := lcshift_byte w in
    let w := map_byte sub_byte w in
    set_byte w 0 (get_byte w 0 + list_get RC n).
    
  Definition gen_round_key (w : key_t) n : key_t :=
    let w0 := get_byte w 0 in
    let w1 := get_byte w 1 in
    let w2 := get_byte w 2 in
    let w3 := get_byte w 3 in
    let w0' := w0 + g n w3 in
    let w1' := w0' + w1 in
    let w2' := w1' + w2 in
    let w3' := w2' + w3 in
    flat [w0'; w1'; w2'; w3'].

  Definition key_schedule : key_schedule_t := flat (iter_collect gen_round_key 10 key [key]).

  Definition get_round_key (n : nat) : b128 := get 128 key_schedule n.

  Definition matrix A := list (list A).

  Arguments map {A B} _ _.

  Definition trans_mx A def (mx : matrix A) (m n : nat) : matrix A :=
    for_n n (fun j => 
      flip map mx (fun row =>
        nth j row def)).

  Definition to_row_major_mx A (m n : nat) (ls : list A) : matrix A := slice n ls.

  Definition to_col_major_mx A def (m n : nat) (ls : list A) : matrix A := trans_mx def (to_row_major_mx n m ls) n m.

  Definition of_row_major_mx A (mx : matrix A) (m n : nat) : list A := flat mx.

  Definition of_col_major_mx A def (mx : matrix A) (m n : nat) : list A := of_row_major_mx (trans_mx def mx m n) n m.

  Definition mx_mul A (def : A) (add mul : A -> A -> A) (a : matrix A) (m n : nat) (b : matrix A) (r : nat) : matrix A :=
    let b := trans_mx def b n r in
    flip mapi a (fun i arow =>
      flip mapi b (fun j bcol =>
        sum def add (map2 mul arow bcol))).                

  Definition shift_rows (mx : matrix byte) := mapi (fun n row => lcshift n row) mx.

  Definition mix_matrix : matrix byte := to_row_major_mx 4 4 (map byte_of_nat
  [ 
    2; 3; 1; 1;
    1; 2; 3; 1;
    1; 1; 2; 3;
    3; 1; 1; 2
  ]).

  Definition f231 A B C D (f : A -> B -> C -> D) b c a := f a b c.

  Definition rshift n (v : bitvec) := zeros n ++ firstn (length v - n) v.

  Arguments fst {A B} _.
  Arguments fold_left {A B} _ _ _.

  Definition gf_mul n R (a b : bitvec) : bitvec :=
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
    
  Definition gf8_byte_mul (a b : byte) : byte := gf_mul 8 "11011" (rev a) (rev b).

  Definition mix_rows (mx : matrix byte) := @mx_mul byte 0 xor gf8_byte_mul mix_matrix 4 4 mx 4.

  Definition add_round_key (text : b128) (round_key : b128) := text + round_key.

  Definition round (bits : b128) (round_key : b128) :=
    let bytes := slice 8 bits in
    let bytes := sub_bytes bytes in
    let mx := @to_col_major_mx byte 0 4 4 bytes in
    let mx := shift_rows mx in
    let mx := mix_rows mx in
    let bytes := @of_col_major_mx byte 0 mx 4 4 in
    let bits := flat bytes in
    add_round_key bits round_key.
  
  Definition encrypt (plaintext : b128) := 
    iter 
      (fun acc n => round acc (get_round_key (S n))) 
      10
      (add_round_key plaintext (get_round_key 0)).

End AES.

Definition p1 := bitvec_of_hex "32 43 f6 a8 88 5a 30 8d 31 31 98 a2 e0 37 07 34".
Definition k1 := bitvec_of_hex "2b 7e 15 16 28 ae d2 a6 ab f7 15 88 09 cf 4f 3c".
Definition c1 := encrypt k1 p1.

Eval compute in (intersperse_every 8 " " $ bitvec_to_hex $ key_schedule k1).
Eval compute in (bitvec_to_hex c1).