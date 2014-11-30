Set Implicit Arguments.

(* AES with 128-bit key *)

Section AES.

  Definition bitvec := list bool.
  
  Definition b128 := bitvec.

  Definition b352 := bitvec.
  
  Definition b32 := bitvec.

  Definition byte := bitvec.

  Require Import List.

  Definition get_slice A (vec : list A) start len := firstn len (skipn start vec).

  Definition get (width : nat) (vec : bitvec) (idx : nat) := get_slice vec (width * idx) width.

  Definition set_slice A (vec : list A) start value := firstn start vec ++ value ++ skipn (start + length value) vec.

  Definition set (width : nat) (vec : bitvec) (idx : nat) value := set_slice vec (width * idx) value.

  Definition key_t := b128.

  Variable key : key_t.

  Definition key_schedule_t := b352.

  (* a specialize version of fold_left for [0,1,...,n-1] *)
  Fixpoint repeat' i A (f : A -> nat -> A) n init :=
    match n with
      | 0 => init
      | S n' => repeat' (S i) f n' (f init i)
    end.

  Definition repeat := repeat' 0.

  Require Import String.
  Open Scope string_scope.

  Definition parse_hex (str : string) : bitvec.
    admit.
  Defined.

  Coercion parse_hex : string >-> bitvec.

  Import ListNotations.
  Open Scope list_scope.

  Definition s_box : list byte := map parse_hex
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

  Definition inv_s_box : list byte := map parse_hex
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

  Definition RC : list byte := map parse_hex
  [ 
    "01"; "02"; "04"; "08"; "10"; "20"; "40"; "80"; "1b"; "36" 
  ].

  Definition list_get (vec : bitvec) idx := nth idx vec false.

  (*here*)
  Definition sub_type (b : type) := list_get s_box (to_nat b).

  Definition sub_bytes := map_byte sub_byte.

  Definition get_byte := get 8.
  Definition set_byte := set 8.

  Definition g n (w : key_t) :=
    let w := left_shift_byte w in
    let w := map_byte sub_byte w in
    set_byte w 0 (get_byte w 0 + RC n).
    
  Definition gen_round_key n (w : key_t) :=
    let w0 := get_byte w 0 in
    let w1 := get_byte w 1 in
    let w2 := get_byte w 2 in
    let w3 := get_byte w 3 in
    let w0' := w0 + g n w3 in
    let w1' := w0' + w1 in
    let w2' := w1' + w2 in
    let w3' := w2' + w3 in
    to_word w0' w1' w2' w3'.

  Definition key_schedule : key_schedule_t := 
    repeat 
      (fun p n => 
         let w := fst p in 
         let res := snd p in 
         set_round_key res (S n) (gen_round_key n w)) 
      10 (key, (set_round_key 0 0 key)).

  Definition get_round_key (n : nat) : b128 := get 128 key_schedule n.

  Definition shift_rows (text : b128) := text *m shift_matrix.

  Definition mix_rows (text : b128) := mix_matrix *m text.

  Definition add_round_key (text : b128) (round_key : b128) := text + round_key.

  Definition round (text : b128) (round_key : b128) :=
    let text := sub_bytes text in
    let text := shift_rows text in
    let text := mix_rows text in
    text := add_round_key text round_key.
  
  Definition encrypt round_n (plaintext : plaintext_t) := repeat (fun acc n => round acc (get_round_key (S n))) round_n (add_round_key plaintext (get_round_key 0)).

  Fixpoint encrypt' round_n (plaintext : plaintext_t) :=
    match round_n with
      | 0 => 
      | S n' => 
        let pre := encrypt' n' plaintext
  


