Section network.
  Context {inVar outVar : Type -> Type}.

  Record channel {t} := {chIn : inVar t; chOut : outVar t}.
  Arguments channel : default implicits.

  CoInductive network : Type :=
  | DoRecv {t} : inVar t -> (t -> network) -> network
  | DoSend {t} : outVar t -> t -> network -> network
  | Parallel : network -> network -> network
  | NewChannel {t} : (channel t -> network) -> network
  | Done.
End network.

Arguments channel {inVar outVar} t.
Arguments network : default implicits.

Notation "'recv' x 'from' ch , p" := (DoRecv ch (fun x => p)) (at level 200, right associativity).
Notation "'send' x 'to' ch , p" := (DoSend ch x p) (at level 200, right associativity).
Notation "p | q" := (Parallel p q) (at level 200, right associativity).
Notation "'new' v0 .. v1 , p" :=
  (NewChannel (fun v0 => .. (NewChannel (fun v1 => p)) ..))
    (at level 200, v0 binder, v1 binder, right associativity).

Section Demo.

  Context {inVar outVar : Type -> Type}.

  (* Ping-pong example. *)
  Definition pingpong {t} (x : t) : network inVar outVar :=
    new a b,
    send x to chOut a,
    (cofix loop := recv y from chIn a, send y to chOut b, loop) |
    (cofix loop := recv y from chIn b, send y to chOut a, loop).

  (* “Game” example from meeting. *)
  Section Game.
    Require Import Ascii.

    Variable keyboard : inVar ascii.
    Variable video : outVar (nat * nat * bool).

    Definition game : network inVar outVar :=
      (cofix loop n := recv _ from keyboard, send (n, n, true) to video, loop (n + 1))
        0.
  End Game.

End Demo.
