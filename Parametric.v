(* An even simpler take on handler code, based on parametricity *)

Require Import List.

Set Implicit Arguments.

Section handler.
  Variables input output : Type.

  Definition handler := input -> list output.
End handler.

(* A simple policy on what values may be sent to a channel:
   ___     _________
  |   |   |         |
  | ? |-->| n <= 5? |--> output
  |___|   |_________|
*)
Module SendLe5.
  (* An implementation of the "?" box has this type. *)
  Definition Sender := forall output,
    handler nat output (* This is the "channel" to the filtering box. *)
    -> handler unit output.

  Inductive output :=
  | SendNat (n : nat).

  (* This function builds the final system. *)
  Definition System (sender : Sender) : handler unit output :=
    sender _ (fun n => SendNat n :: nil).
End SendLe5.

(* A simple information-flow policy:
             _________________     ___
  input1 -->|                 |   |   |
            | input1 + input2 |-->| ? |--> output
  input2 -->|_________________|   |___|
*)
Module OnlySum.
  Inductive output :=
  | SendNat (n : nat).

  (* An implementation of the "?" box has this type. *)
  Definition Receiver := handler nat output.

  (* This function builds the final system. *)
  Definition System (receiver : Receiver) : handler (nat * nat) output :=
    fun p => receiver (fst p + snd p).
End OnlySum.
