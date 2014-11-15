(* An even simpler take on handler code, based on parametricity *)

Require Import List.

Set Implicit Arguments.

Section handler.
  Variables input output : Type.

  Definition handler := input -> list output.

  Definition statefulHandler :=  { state : Type & state * input -> state * list output }.
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

  Require Import Arith.

  (* This function builds the final system. *)
  Definition System (sender : Sender) : handler unit output :=
    sender _ (fun n => if le_lt_dec n 5 then SendNat n :: nil else nil).
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

Require Import String.

Module PwMgr.
  Variables displayAction plaintext cyphertext : Type.

  Variable encrypt : plaintext -> cyphertext.
  Variable decrypt : cyphertext -> plaintext.

  Record Gui := {
    guiState : Type;
    OnMouseClick : guiState -> nat -> nat -> guiState * option plaintext;
    OnNewMessage : guiState -> plaintext -> guiState * option displayAction * option plaintext
  }.

  Record Network := {
    networkState : Type;
    OnMessage : networkState -> cyphertext -> networkState * option cyphertext;
    OnRequestToSend : networkState -> cyphertext -> networkState * option cyphertext
  }.

  Record System := {
    systemState : Type;
    OnRecv : systemState -> cyphertext -> systemState * option cyphertext * option displayAction;
    OnMouseclick : systemState -> nat -> nat -> systemState * option cyphertext * option displayAction
  }.

  (*
  Definition system (gui : Gui) (network : Network) : System := {|
    systemState := (guiState gui * networkState network)%Type;
    OnRecv := fun sts ct => 


  Inductive guiEvent :=
  | MouseClick (x y : nat).

  Definition Gui := forall output,
                      statefulHandler string output
                      -> statefulHandler guiEvent output.

  Inductive output :=
  | NetM
  
  Axiom encrypt : nat -> string -> 

  Definition System (gui : Gui) : handler guiEvent output :=
    *)
End PwMgr.

