Set Implicit Arguments.

Require Import FPUtil.

(* AES with 128-bit key *)

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

Definition key_schedule_t := b352.

Definition zeros := repeat false.

Definition of_bin_ascii (ch : ascii) :=
  (match ch with
     | "0" => false
     | _ => true
   end)%char.

Definition bitvec_of_bin_str : string -> bitvec := map of_bin_ascii << str_to_list.

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

Goal bitvec_to_nat "1100" = 3. r. Qed.

(* byte is in MSB-first format *)

Arguments rev {A} _.

Definition byte_of_N (n : N) : byte := 
  rev $ trunc_pad_to 8 (bitvec_of_N n).

Definition byte_of_nat (n : nat) : byte := byte_of_N (N.of_nat n).
Coercion byte_of_nat : nat >-> byte.

Goal byte_of_nat 3 = "00000011" :> bitvec. r. Qed.

Definition byte_to_nat (b : byte) : nat := bitvec_to_nat $ rev b.

Definition N_of_hex_ascii (ch : ascii) : N := default 0%N $ msum $ map (fun x : ascii * ascii * N => let (p, base) := x in N_of_ascii_in (fst p) (snd p) base ch) [("0", "9", 0%N); ("A", "F", 10%N); ("a", "f", 10%N)]%char.

Definition map_byte (f : byte -> byte) (vec : bitvec) : bitvec := map_every 8 f vec.

(* hex string is in bytewise-MSB-first format *)
Definition halfbyte_of_hex_ascii := rev << trunc_pad_to 4 << bitvec_of_N << N_of_hex_ascii.

Definition remove_space (ch : ascii) :=
  match ch with
    | " "%char => false
    | _ => true
  end.

Definition bitvec_of_hex : string -> bitvec := flat << map halfbyte_of_hex_ascii << filter remove_space << str_to_list.

Definition left_trunc_pad_to n := rev << trunc_pad_to n << rev.

Definition byte_of_hex : string -> byte := left_trunc_pad_to 8 << bitvec_of_hex.

Definition halfbyte_to_hex (v : bitvec) : ascii :=
  let n := bitvec_to_nat (rev v) in
  let n0 := nat_of_ascii "0" in
  let nA := nat_of_ascii "A" in
  if n <? 10 then
    ascii_of_nat (n0 + n)
  else
    ascii_of_nat (nA + n - 10).

Goal halfbyte_to_hex "1011" = "B"%char. r. Qed.

Definition bitvec_to_hex := list_to_str << map halfbyte_to_hex << slice 4.

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

Goal nth 1 s_box 0 = "01111100" :> bitvec. r. Qed.
Goal nth 16 s_box 0 = "11001010" :> bitvec. r. Qed.
Goal bitvec_to_hex (nth 1 s_box 0) = "7C". r. Qed.
Goal bitvec_to_hex (nth 16 s_box 0) = "CA". r. Qed.

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

Notation hex := bitvec_of_hex.
Notation show := bitvec_to_hex.

Goal (map_byte sub_byte $ hex "cf4f3c09") = hex "8a84eb01". r. Qed.

Definition get_byte := get 8.
Definition set_byte := set 8.

Definition lcshift_byte := @lcshift bool 8.

Goal (lcshift_byte $ hex "09cf4f3c") = hex "cf4f3c09". r. Qed.

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

Goal (g 0 $ hex "09cf4f3c") = hex "8b84eb01". r. Qed.

Definition gen_round_key (w : key_t) n : key_t :=
  let w0 := get 32 w 0 in
  let w1 := get 32 w 1 in
  let w2 := get 32 w 2 in
  let w3 := get 32 w 3 in
  let w0' := w0 + g n w3 in
  let w1' := w0' + w1 in
  let w2' := w1' + w2 in
  let w3' := w2' + w3 in
  flat [w0'; w1'; w2'; w3'].

Declare Reduction c := vm_compute.

Definition test_key := hex "2b7e1516 28aed2a6 abf71588 09cf4f3c".
Goal (flip gen_round_key 0 $ test_key) = hex "a0fafe17 88542cb1 23a33939 2a6c7605". r. Qed.

Definition key_schedule (key : key_t) : key_schedule_t := flat (iter_collect gen_round_key 10 key [key]).

Definition test_key_schedule := key_schedule test_key.
Goal (get 128 test_key_schedule 10) = hex "d014f9a8 c9ee2589 e13f0cc8 b6630ca6". r. Qed.

Definition get_round_key (key : key_t) (n : nat) : b128 := get 128 (key_schedule key) n.

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

Definition test_mx := to_row_major_mx 4 4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].
Definition test_mx_mx := [[90; 100; 110; 120]; [202; 228; 254; 280]; [314; 356; 398; 440]; [426; 484; 542; 600]].
Goal (mx_mul 0 plus mult test_mx 4 4 test_mx 4) = test_mx_mx. r. Qed.
Definition test_mx_mx' := [[30; 70; 110; 150]; [70; 174; 278; 382]; [110; 278; 446; 614]; [150; 382; 614; 846]].
Goal (mx_mul 0 plus mult test_mx 4 4 (trans_mx 0 test_mx 4 4) 4) = test_mx_mx'. r. Qed.

Definition shift_rows (mx : matrix byte) := mapi (fun n row => lcshift n row) mx.

Definition mix_matrix : matrix byte := to_row_major_mx 4 4 $ map byte_of_nat
[ 
  2; 3; 1; 1;
  1; 2; 3; 1;
  1; 1; 2; 3;
  3; 1; 1; 2
].

Definition inv_mix_matrix : matrix byte := to_row_major_mx 4 4 $ slice 8 $ flat $ map hex
[
  "0e 0b 0d 09";
  "09 0e 0b 0d";
  "0d 09 0e 0b";
  "0b 0d 09 0e"
].

Definition f231 A B C D (f : A -> B -> C -> D) b c a := f a b c.

Definition rshift n (v : bitvec) := zeros n ++ firstn (length v - n) v.

Arguments fst {A B} _.
Arguments fold_left {A B} _ _ _.

Definition gf_mul n R (a b : bitvec) : bitvec :=
  let R := trunc_pad_to n R in
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

Definition gf8_byte_mul (a b : byte) : byte := rev $ gf_mul 8 "11011" (rev a) (rev b).

Definition mix_rows (mx : matrix byte) := @mx_mul byte 0 xor gf8_byte_mul mix_matrix 4 4 mx 4.

Definition add_round_key (text : b128) (round_key : b128) := text + round_key.

Definition round (is_last : bool) (bits : b128) (round_key : b128) :=
  let mx := @to_col_major_mx byte 0 4 4 (slice 8 bits) in
  let mx := map (map sub_byte) mx in
  let mx := shift_rows mx in
  let mx := if is_last then mx else mix_rows mx in
  let round_key_mx := @to_col_major_mx byte 0 4 4 (slice 8 round_key) in
  let mx := map2 (map2 add_round_key) mx round_key_mx in 
  flat (@of_col_major_mx byte 0 mx 4 4).

Definition test_plain := hex "32 43 f6 a8 88 5a 30 8d 31 31 98 a2 e0 37 07 34".

Definition test_r1 := hex "19 3d e3 be a0 f4 e2 2b 9a c6 8d 2a e9 f8 48 08".
Goal test_plain + get_round_key test_key 0 = test_r1. r. Qed.
Definition test_r1_after_sb := hex "d4 27 11 ae e0 bf 98 f1 b8 b4 5d e5 1e 41 52 30".
Goal (slice 8 >> map sub_byte >> flat $ test_r1) = test_r1_after_sb. r. Qed.
Definition test_r1_after_sb_mx := map (map hex) [["D4"; "E0"; "B8"; "1E"]; ["27"; "BF"; "B4"; "41"]; ["11"; "98"; "5D"; "52"]; ["AE"; "F1"; "E5"; "30"]]. 
Goal (slice 8 >> @to_col_major_mx byte 0 4 4 $ test_r1_after_sb) = test_r1_after_sb_mx. r. Qed.
Definition test_r1_after_shift := map (map hex) [["D4"; "E0"; "B8"; "1E"]; ["BF"; "B4"; "41"; "27"]; ["5D"; "52"; "11"; "98"]; ["30"; "AE"; "F1"; "E5"]].
Goal (shift_rows $ test_r1_after_sb_mx) = test_r1_after_shift. r. Qed.
Definition test_r1_after_mix := map (map hex) [["04"; "E0"; "48"; "28"]; ["66"; "CB"; "F8"; "06"]; ["81"; "19"; "D3"; "26"]; ["E5"; "9A"; "7A"; "4C"]].
Goal (mix_rows $ test_r1_after_shift) = test_r1_after_mix. r. Qed.
Definition test_roundkey1 := get_round_key test_key 1.
Definition test_r1_final := hex "a4 9c 7f f2 68 9f 35 2b 6b 5b ea 43 02 6a 50 49".
Goal (round false test_r1 test_roundkey1) = test_r1_final. r. Qed.
Definition test_r2_final := hex "aa 8f 5f 03 61 dd e3 ef 82 d2 4a d2 68 32 46 9a".
Goal (round false test_r1_final (get_round_key test_key 2)) = test_r2_final. r. Qed.

Definition encrypt (key : key_t) (plaintext : b128) := 
  let keys := slice 128 (key_schedule key) in
  let get_key n := nth n keys (zeros 128) in
  let after0 := add_round_key plaintext (get_key 0) in
  let after9 := fold_left (round false) (range 1 9 keys) after0 in
  round true after9 (get_key 10).

Definition test_cipher := hex "39 25 84 1d 02 dc 09 fb dc 11 85 97 19 6a 0b 32".
Goal encrypt test_key test_plain = test_cipher. r. Qed.

Definition test_plain2 := hex "00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff".
Definition test_key2 := hex "00 01 02 03 04 05 06 07 08 09 0a 0b 0c 0d 0e 0f".
Definition test_cipher2 := hex "69 c4 e0 d8 6a 7b 04 30 d8 cd b7 80 70 b4 c5 5a".
Goal encrypt test_key2 test_plain2 = test_cipher2. r. Qed.

Definition test_plain3 := hex "00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00".
Definition test_key3 := hex "00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00".
Definition test_cipher3 := hex "66 e9 4b d4 ef 8a 2c 3b 88 4c fa 59 ca 34 2b 2e".
Goal encrypt test_key3 test_plain3 = test_cipher3. r. Qed.

Definition test_plain4 := hex "00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00".
Definition test_key4 := hex "00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 01".
Definition test_cipher4 := hex "05 45 aa d5 6d a2 a9 7c 36 63 d1 43 2a 3d 1c 84".
Goal encrypt test_key4 test_plain4 = test_cipher4. r. Qed.

Definition test_plain5 := hex "00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 01".
Definition test_key5 := hex "00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00".
Definition test_cipher5 := hex "58 e2 fc ce fa 7e 30 61 36 7f 1d 57 a4 e7 45 5a".
Goal encrypt test_key5 test_plain5 = test_cipher5. r. Qed.

Definition inv_shift_rows (mx : matrix byte) := mapi (fun n row => rcshift n row) mx.

Definition inv_sub_byte (b : byte) := list_get inv_s_box (byte_to_nat b).

Definition inv_mix_rows (mx : matrix byte) := @mx_mul byte 0 xor gf8_byte_mul inv_mix_matrix 4 4 mx 4.

Definition inv_round (is_last : bool) (bits : b128) (round_key : b128) :=
  let mx := @to_col_major_mx byte 0 4 4 (slice 8 bits) in
  let mx := inv_shift_rows mx in
  let mx := map (map inv_sub_byte) mx in
  let round_key_mx := @to_col_major_mx byte 0 4 4 (slice 8 round_key) in
  let mx := map2 (map2 add_round_key) mx round_key_mx in 
  let mx := if is_last then mx else inv_mix_rows mx in
  flat (@of_col_major_mx byte 0 mx 4 4).

Definition decrypt (key : key_t) (ciphertext : b128) := 
  let keys := slice 128 (key_schedule key) in
  let get_key n := nth n keys (zeros 128) in
  let after0 := add_round_key ciphertext (get_key 10) in
  let after9 := fold_left (inv_round false) (rev $ range 1 9 keys) after0 in
  inv_round true after9 (get_key 0).

Goal decrypt test_key test_cipher = test_plain. r. Qed.
Goal decrypt test_key2 test_cipher2 = test_plain2. r. Qed.
Goal decrypt test_key3 test_cipher3 = test_plain3. r. Qed.
Goal decrypt test_key4 test_cipher4 = test_plain4. r. Qed.
Goal decrypt test_key5 test_cipher5 = test_plain5. r. Qed.
