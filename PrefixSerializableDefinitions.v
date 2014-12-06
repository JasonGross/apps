Require Import Coq.Strings.String Coq.Relations.Relation_Definitions Coq.Classes.RelationClasses.

Set Implicit Arguments.

Local Open Scope string_scope.

Class Serializable A :=
  { to_string : A -> string }.
Class Deserializable A :=
  { from_string : string -> option A * string }.

Definition option_lift_relation {A B} (f : A -> B -> Prop) (a : option A) (b : option B)
: Prop
  := match a, b with
       | Some a', Some b' => f a' b'
       | None, None => True
       | _, _ => False
     end.

Instance option_lift_relation_refl {A R} `{Reflexive A R} : Reflexive (option_lift_relation R).
Proof.
  repeat (intros [] || intro); hnf; eauto.
Defined.

Instance option_lift_relation_sym {A R} `{Symmetric A R} : Symmetric (option_lift_relation R).
Proof.
  repeat (intros [] || intro); hnf; eauto.
Defined.

Instance option_lift_relation_trans {A R} `{Transitive A R} : Transitive (option_lift_relation R).
Proof.
  repeat (intros [] || intro); hnf; eauto.
Defined.

Class PrefixSerializable A (R : relation A) :=
  { serialize :> Serializable A;
    deserialize :> Deserializable A;
    from_to_string : forall x, option_lift_relation R (fst (from_string (to_string x))) (Some x) /\ snd (from_string (to_string x)) = "";
    prefix_closed : forall s1 s2 x, option_lift_relation R (fst (from_string s1)) (Some x) -> option_lift_relation R (fst (from_string (s1 ++ s2))) (Some x) /\ snd (from_string (s1 ++ s2)) = snd (from_string s1) ++ s2 }.

Arguments PrefixSerializable : clear implicits.

Definition from_to_string_1 {A R} `{PrefixSerializable A R} x := proj1 (from_to_string x).
Definition from_to_string_2 {A R} `{PrefixSerializable A R} x := proj2 (from_to_string x).
Definition prefix_closed_1 {A R} `{PrefixSerializable A R} s1 s2 x H
  := proj1 (prefix_closed s1 s2 x H).
Definition prefix_closed_2 {A R} `{PrefixSerializable A R} s1 s2 x H
  := proj2 (prefix_closed s1 s2 x H).

Definition from_to_string_1_eq {A} `{PrefixSerializable A eq} x
: fst (from_string (to_string x)) = Some x.
Proof.
  pose proof (from_to_string_1 x) as H'.
  hnf in H'; simpl in *.
  destruct (fst (from_string (to_string x))); subst; tauto.
Qed.
Definition prefix_closed_1_eq {A} `{PrefixSerializable A eq} s1 s2 x
: fst (from_string s1) = Some x -> fst (from_string (s1 ++ s2)) = Some x.
Proof.
  intro H'.
  pose proof (prefix_closed_1 s1 s2 x).
  destruct (fst (from_string s1)); simpl in *; try congruence.
  destruct (fst (from_string (s1 ++ s2))); simpl in *; try congruence.
  inversion H'; intuition (subst; eauto).
Qed.
Definition prefix_closed_2_refl {A R} `{Reflexive A R} `{PrefixSerializable A R} s1 s2 x
: fst (from_string s1) = Some x -> snd (from_string (s1 ++ s2)) = snd (from_string s1) ++ s2.
Proof.
  intro H'.
  eapply prefix_closed_2.
  rewrite H'.
  reflexivity.
Qed.

Arguments serialize _ _ !_ / .
Arguments deserialize _ _ !_ / .
