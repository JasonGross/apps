Set Implicit Arguments.
Require Import Process.
Require Import PiCalculus2.

Inductive HDirection := Left | Right.
Inductive VDirection := Up | Down.

Inductive Event :=
| Keyboard (_ : HDirection)
| Timer
.

Definition Point := (nat * nat)%type.

Record State := {
  ballPos : Point;
  ballHDir : HDirection;
  ballVDir : VDirection;
  paddlePos : nat
}.

Definition Output := list Point.

Definition SCREEN_WIDTH := 80.
Definition SCREEN_HEIGHT := 60.
Definition PADDLE_LEN := 7.

Infix "==" := EqNat.beq_nat (at level 70).

Definition upd_paddlePos st v := {| 
  ballPos := ballPos st; 
  ballHDir := ballHDir st;
  ballVDir := ballVDir st;
  paddlePos := v
|}.

Require Import List.
Import ListNotations.

Fixpoint drawHLine x y len : Output :=
  match len with
    | 0 => nil
    | S len' => (x, y) :: drawHLine (x + 1) y len'
  end.

Definition draw (st : State) : Output :=
  ballPos st :: drawHLine (paddlePos st) (SCREEN_HEIGHT - 1) PADDLE_LEN.

Definition handler (st : State) (e : Event) : State * Output :=
  let st' :=
      match e with
        | Keyboard Left =>
          let paddlePos' := paddlePos st - 1 in
          upd_paddlePos st paddlePos'
        | Keyboard Right =>
          let paddlePos' := max (paddlePos st + 1) (SCREEN_WIDTH - PADDLE_LEN) in
          upd_paddlePos st paddlePos'
        | Timer => st (* unimplemented *)
      end in
  (st', draw st').

CoFixpoint game st := #?["events", e], let (st', out) := handler st e in #!["screen", out], game st'.