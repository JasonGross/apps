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

Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").

(** [atomic x] is the same as [idtac] if [x] is a variable or hypothesis, but is [fail 0] if [x] has internal structure. *)
Ltac atomic x :=
  idtac;
  match x with
    | _ => is_evar x; fail 1 x "is not atomic (evar)"
    | ?f _ => fail 1 x "is not atomic (application)"
    | (fun _ => _) => fail 1 x "is not atomic (fun)"
    | forall _, _ => fail 1 x "is not atomic (forall)"
    | let x := _ in _ => fail 1 x "is not atomic (let in)"
    | match _ with _ => _ end => fail 1 x "is not atomic (match)"
    | _ => is_fix x; fail 1 x "is not atomic (fix)"
    | context[?E] => (* catch-all *) (not constr_eq E x); fail 1 x "is not atomic (has subterm" E ")"
    | _ => idtac
  end.

(** given a [matcher] that succeeds on some hypotheses and fails on
    others, destruct any matching hypotheses, and then execute [tac]
    after each [destruct].
    The [tac] part exists so that you can, e.g., [simpl in *], to
    speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in *).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(* matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

Ltac destruct_sig_matcher HT :=
  match eval hnf in HT with
    | ex _ => idtac
    | ex2 _ _ => idtac
    | sig _ => idtac
    | sig2 _ _ => idtac
    | sigT _ => idtac
    | sigT2 _ _ => idtac
    | and _ _ => idtac
    | prod _ _ => idtac
  end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.
Ltac destruct_sig' := destruct_all_matches' destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_sig_matcher HT || destruct_sig_matcher HT
).

(** if progress can be made by [exists _], but it doesn't matter what
    fills in the [_], assume that something exists, and leave the two
    goals of finding a member of the apropriate type, and proving that
    all members of the appropriate type prove the goal *)
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @sigT;
  match goal with
(*    | [ |- @sig ?T _ ] => destruct_exists' T*)
    | [ |- @sigT ?T _ ] => destruct_exists' T
(*    | [ |- @sig2 ?T _ _ ] => destruct_exists' T*)
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
  end.

(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
    | [ H : T |- _ ] => fail 1
    | _ => pose proof defn
  end.

(** [pose defn], but only if that hypothesis doesn't exist *)
Tactic Notation "unique" "pose" constr(defn) :=
  match goal with
    | [ H := defn |- _ ] => fail 1
    | _ => pose defn
  end.
