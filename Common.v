Definition pull_if_dep {A B} (P : forall b : bool, A b -> B b) (a : A true) (a' : A false)
           (b : bool)
: P b (if b as b return A b then a else a') =
  if b as b return B b then P _ a else P _ a'
  := match b with true => eq_refl | false => eq_refl end.

Definition pull_if {A B} (P : A -> B) (a a' : A) (b : bool)
: P (if b then a else a') = if b then P a else P a'
  := pull_if_dep (fun _ => P) a a' b.

(** find the head of the given expression *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

Ltac evar1_aware_destruct_bool x :=
  instantiate (1 := if x then _ else _);
  destruct x.
