Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Program.Program.

Set Implicit Arguments.

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

Lemma Some_inj {A} {a b : A} (H : Some a = Some b) : a = b.
Proof.
  congruence.
Qed.

Local Open Scope bool_scope.

Lemma fold_left_andb_false {A} (f : A -> bool) (ls : list A)
: fold_left (fun b x => b && f x) ls false = false.
Proof.
  induction ls; simpl; trivial.
Qed.

Lemma fold_left_andb_true_init {A} {f : A -> bool} {ls : list A} {b}
: fold_left (fun b x => b && f x) ls b = true -> b = true.
Proof.
  destruct b; try reflexivity.
  rewrite fold_left_andb_false; intro H; inversion H.
Qed.

Lemma fold_left_andb_true {A} (f : A -> bool) (ls : list A)
: fold_left (fun b x => b && f x) ls true = true
  <-> (forall x, List.In x ls -> f x = true).
Proof.
  induction ls; simpl.
  { split; intros; tauto. }
  { split; destruct_head iff; intros;
    destruct_head or; subst;
    repeat match goal with
             | [ H : false = true |- _ ] => solve [ inversion H ]
             | [ H : true = false |- _ ] => solve [ inversion H ]
             | [ |- ?b = true ] => case_eq b; [ reflexivity | intro; exfalso ]
             | [ H : fold_left _ ?ls false = true |- _ ] => rewrite fold_left_andb_false in H
             | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
             | [ H : fold_left _ _ (?f ?x) = true |- _ ]
               => let H' := fresh in
                  pose proof (fold_left_andb_true_init H) as H';
                    rewrite H' in *
             | [ H : forall x, List.In _ _ -> _, H' : List.In _ _ |- _ ] => specialize (H _ H')
             | [ H : forall x, _ = _ \/ List.In _ _ -> _ |- _ ]
               => pose proof (H _ (or_introl eq_refl));
                 pose proof (fun x H' => H x (or_intror H'));
                 clear H
             | [ H : ?a = true, H' : fold_left _ _ ?a = _ |- _ ] => rewrite H in H'
             | _ => congruence
           end. }
Qed.

(** Coq's built in tactics don't work so well with things like [iff]
    so split them up into multiple hypotheses *)
(** We do some hackery with typeclasses to get around the fact that
    Coq 8.4 doesn't have tactics in terms; we want to say
<<
Ltac make_apply_under_binders_in lem H :=
  let tac := make_apply_under_binders_in in
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              $(let ret' := tac lem Hx in
                                exact ret')$) in
         let ret' := (eval cbv zeta in ret) in
         constr:(ret')
    | _ => let ret := constr:($(let H' := fresh in
                                pose H as H';
                                apply lem in H';
                                exact H')$) in
           let ret' := (eval cbv beta zeta in ret) in
           constr:(ret')
  end.
Ltac apply_under_binders_in lem H :=
  let H' := make_apply_under_binders_in lem H in
  let H'' := fresh in
  pose proof H' as H'';
    clear H;
    rename H'' into H.
>> *)

Class make_apply_under_binders_in_helper {T} (lem : T) {T'} (H : T') {T''} := do_make_apply_under_binders_in_helper : T''.

Class make_apply_under_binders_in_helper_helper {T} (H : T) {T'} (lem : T') {T''} := do_make_apply_under_binders_in_helper_helper : T''.

Hint Extern 0 (make_apply_under_binders_in_helper_helper ?H ?lem)
=> let H' := fresh in
   pose H as H';
     apply lem in H';
     exact H'
           : typeclass_instances.

Ltac make_apply_under_binders_in lem H :=
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              _ : make_apply_under_binders_in_helper lem Hx) in
         let ret' := (eval cbv zeta beta delta [do_make_apply_under_binders_in_helper make_apply_under_binders_in_helper] in ret) in
         let retT := type of ret' in
         let retT' := (eval cbv zeta beta delta [do_make_apply_under_binders_in_helper make_apply_under_binders_in_helper] in retT) in
         constr:(ret' : retT')
    | _ => let ret := constr:(_ : make_apply_under_binders_in_helper_helper H lem) in
           let ret' := (eval cbv beta zeta delta [make_apply_under_binders_in_helper_helper do_make_apply_under_binders_in_helper_helper] in ret) in
           let retT := type of ret' in
           let retT' := (eval cbv beta zeta delta [make_apply_under_binders_in_helper_helper do_make_apply_under_binders_in_helper_helper] in retT) in
           constr:(ret' : retT')
  end.

Hint Extern 0 (make_apply_under_binders_in_helper ?lem ?H) =>
let ret := make_apply_under_binders_in lem H
in exact ret
   : typeclass_instances.

Ltac apply_under_binders_in lem H :=
  let H' := make_apply_under_binders_in lem H in
  let H'' := fresh in
  pose proof H' as H'';
    clear H;
    rename H'' into H.

Ltac split_in_context ident proj1 proj2 :=
  repeat match goal with
           | [ H : context[ident] |- _ ] =>
             let H0 := make_apply_under_binders_in proj1 H in
             let H1 := make_apply_under_binders_in proj2 H in
             pose proof H0;
               pose proof H1;
               clear H
         end.

Ltac split_iff := split_in_context iff @proj1 @proj2.
Ltac split_and := split_in_context and @fst @snd.
