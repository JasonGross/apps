Section hlist.
  Context {a : Type} {b : a -> Type}.

  Inductive hlist : list a -> Type :=
  | HNil : hlist nil
  | HCons {x : a} {ls : list a} : b x -> hlist ls -> hlist (x :: ls).

  Definition huncons {x xs} (h : hlist (x :: xs)) :=
    let 'HCons _ _ y h' := h in (y, h').

  Definition match_hnil {r} (x : r) (_ : hlist nil) := x.

  Definition match_hcons {x xs r} (f : b x -> hlist xs -> r) h :=
    let (y, h') := huncons h in f y h'.
End hlist.

Arguments hlist {a} b _.


Section process.
  Context {var : Type -> Type} {input : Type}.

  CoInductive process :=
  | DoRecv : (input -> process) -> process
  | DoSend {output} : var output -> output -> process -> process.
End process.

Arguments process : default implicits.

Notation "'recv' x , k" := (DoRecv (fun x => k)) (at level 200, right associativity).
Notation "'send' x 'to' ch , k" := (DoSend ch x k) (at level 200, right associativity).


Section network.
  Context {var : Type -> Type}.

  Inductive network : Type -> Type :=
  | Var {input} : var input -> network input
  | Mu {inputs input} :
      (hlist var inputs -> hlist network inputs * network input) ->
      network input
  | Node {input} :
      process var input ->
      network input.
End network.

Arguments network : default implicits.

Notation "'net' v0 .. v1 => n0 ; .. ; n1 'in' n" :=
  (Mu (match_hcons (fun v0 => .. (match_hcons (fun v1 => match_hnil (HCons n0 (.. (HCons n1 HNil) ..), n))) ..)))
    (at level 200, v0 binder, v1 binder, right associativity).


Section Demo.

  Context {var : Type -> Type}.

  (* Ping-pong example. *)
  Definition pingpong t : network var t :=
    net a b =>
      Node (cofix loop := recv x, send x to b, loop);
      Node (cofix loop := recv x, send x to a, loop)
    in Var a.

  (* “Game” example from meeting. *)
  Section Game.
    Require Import Ascii.

    Variable video : var (nat * nat * bool).

    Definition game : network var (ascii : Type) :=
      Node ((cofix loop n := recv _, send (n, n, true) to video, loop (n + 1))
              0).
  End Game.

End Demo.
