Require Import Coq.Strings.String Coq.Numbers.Natural.Peano.NPeano Coq.NArith.BinNat Coq.omega.Omega Coq.Setoids.Setoid Coq.Classes.RelationPairs Coq.Lists.SetoidList.
Require Export PrefixSerializableDefinitions.
Require Import Common.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope string_scope.

Local Ltac cleanup' :=
  match goal with
    | _ => reflexivity
    | _ => assumption
    | [ H : ?x = ?x |- _ ] => clear H
    | [ H : true = false |- _ ] => solve [ inversion H ]
    | [ H : false = true |- _ ] => solve [ inversion H ]
    | [ H : Some _ = None |- _ ] => solve [ inversion H ]
    | [ H : None = Some _ |- _ ] => solve [ inversion H ]
    | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
    | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
    | [ H : inl _ = inl _ |- _ ] => (inversion H; clear H)
    | [ H : inr _ = inr _ |- _ ] => (inversion H; clear H)
    | [ H : eqlistA _ (_::_) _ |- _ ] => (inversion H; clear H)
    | [ H : eqlistA _ _ (_::_) |- _ ] => (inversion H; clear H)
    | [ |- Some _ = Some _ ] => apply f_equal
    | [ |- _ /\ _ ] => split
    | [ |- (_, _) = (_, _) ] => apply injective_projections
    | [ H : ?x = Some _, H' : appcontext[match ?x with _ => _ end] |- _ ]
      => rewrite H in H'
    | [ H : ?x = None, H' : appcontext[match ?x with _ => _ end] |- _ ]
      => rewrite H in H'
    | [ H : ?x = Some _, H' : appcontext[?x] |- _ ]
      => let h := head x in not constr_eq h (@Some); rewrite H in H'
    | [ H : ?x = None, H' : appcontext[?x] |- _ ]
      => let h := head x in not constr_eq h (@None); rewrite H in H'
    | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
    | _ => progress subst
    | _ => progress split_and
    | _ => progress destruct_head and
    | _ => progress destruct_head prod
    | _ => progress destruct_head unit
    | _ => progress destruct_head True
    | _ => progress destruct_head False
    | _ => progress destruct_head Empty_set
  end.

Local Ltac cleanup := repeat cleanup'.

Lemma from_to_string_append_1 {A R} `{PrefixSerializable A R} x s : option_lift_relation R (fst (from_string (to_string x ++ s))) (Some x).
Proof.
  apply prefix_closed_1.
  apply from_to_string_1.
Qed.

Lemma from_to_string_append_2 {A R} `{PrefixSerializable A R} x s : snd (from_string (to_string x ++ s)) = s.
Proof.
  erewrite prefix_closed_2 by apply from_to_string_1.
  rewrite from_to_string_2; reflexivity.
Qed.

Lemma from_to_string_append_1_eq {A} `{PrefixSerializable A eq} x s
: fst (from_string (to_string x ++ s)) = Some x.
Proof.
  apply prefix_closed_1_eq.
  apply from_to_string_1_eq.
Qed.

Local Arguments Ascii.ascii_dec !_ !_ / .

Instance Serializable_bool : Serializable bool
  := {| to_string b := if b : bool then "1" else "0" |}.
Instance Deserializable_bool : Deserializable bool
  := {| from_string x := match x with
                           | "" => (None, "")
                           | String a s' => if Ascii.ascii_dec a "1"
                                            then (Some true, s')
                                            else if Ascii.ascii_dec a "0"
                                                 then (Some false, s')
                                                 else (None, x)
                         end |}.

Instance PrefixSerializable_bool {R} `{Reflexive bool R}
: PrefixSerializable bool R
  := {| serialize := _; deserialize := _ |}.
Proof.
  intros []; split; reflexivity.
  abstract (
      intro s1; induction s1; intros;
      repeat match goal with
               | _ => progress cleanup
               | [ b : bool |- _ ] => destruct b
               | _ => progress simpl in *
               | _ => progress unfold from_string, to_string in *
               | [ |- appcontext[prefix _ ?s] ] => (atomic s; destruct s)
               | [ H : appcontext[prefix _ ?s] |- _ ] => (atomic s; destruct s)
               | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
               | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
             end
    ).
Defined.

Local Opaque Serializable_bool.
Local Opaque Deserializable_bool.

Fixpoint string_of_Npositive (n : positive) : string :=
  match n with
    | xH => "1"
    | xI n' => string_of_Npositive n' ++ "1"
    | xO n' => string_of_Npositive n' ++ "0"
  end.

Definition string_of_N (n : N) : string :=
  match n with
    | N0 => "0 "
    | Npos n' => string_of_Npositive n' ++ " "
  end.

Fixpoint N_of_string_helper (s : string) (so_far : N) (acc : string) : option N * string :=
  match s with
    | "" => (None, acc)
    | String a s' => if Ascii.ascii_dec a " "
                     then (Some so_far, s')
                     else if Ascii.ascii_dec a "0"
                          then N_of_string_helper s' (2 * so_far) (acc ++ String a "")
                          else if Ascii.ascii_dec a "1"
                               then N_of_string_helper s' (1 + 2 * so_far) (acc ++ String a "")
                               else (None, acc ++ String a s')
  end.

Definition N_of_string (s : string) : option N * string := N_of_string_helper s 0 "".

Arguments string_of_N !n / .
Arguments N_of_string !s / .
Arguments N_of_string_helper !s so_far acc / .

Lemma string_append_assoc (s1 s2 s3 : string) : (s1 ++ s2) ++ s3 = s1 ++ (s2 ++ s3).
Proof.
  revert s2 s3.
  induction s1; simpl; trivial.
  intros; f_equal; eauto.
Qed.

Local Ltac N_str_append_t IH :=
  repeat match goal with
           | _ => progress simpl in *
           | _ => progress cleanup
           | _ => progress subst
           | _ => intro
           | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
           | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
           | [ H : _ |- _ ] => rewrite H by assumption
           | [ |- appcontext[match ?E with _ => _ end] ] => atomic E; destruct E
           | _ => rewrite !string_append_assoc
           | _ => rewrite IH; clear IH
         end.

Lemma N_of_string_append0 (s1 : string) (n1 : N) so_far acc
      (H1 : N_of_string_helper (s1 ++ " ") so_far acc = (Some n1, ""))
      (H1' : N_of_string_helper s1 so_far acc = (None, acc ++ s1))
: N_of_string_helper (s1 ++ "0 ") so_far acc = (Some (2 * n1)%N, "").
Proof.
  generalize dependent so_far; generalize dependent acc.
  induction s1; simpl in *;
  N_str_append_t IHs1.
Qed.

Lemma N_of_string_append1 (s1 : string) (n1 : N) so_far acc
      (H1 : N_of_string_helper (s1 ++ " ") so_far acc = (Some n1, ""))
      (H1' : N_of_string_helper s1 so_far acc = (None, acc ++ s1))
: N_of_string_helper (s1 ++ "1 ") so_far acc = (Some (1 + 2 * n1)%N, "").
Proof.
  generalize dependent so_far; generalize acc;
  induction s1; simpl in *;
  N_str_append_t IHs1.
Qed.

Delimit Scope char_scope with char.
Bind Scope char_scope with Ascii.ascii.

Fixpoint string_contains_ascii (s : string) (a : Ascii.ascii) : bool :=
  match s with
    | "" => false
    | String a' s' => if Ascii.ascii_dec a a'
                      then true
                      else string_contains_ascii s' a
  end.

Lemma string_contains_ascii_append s1 s2 a
: string_contains_ascii (s1 ++ s2) a = string_contains_ascii s1 a || string_contains_ascii s2 a.
Proof.
  induction s1; simpl; trivial.
  rewrite IHs1; clear IHs1.
  edestruct Ascii.ascii_dec; trivial.
Qed.

Lemma string_append_empty s : s ++ "" = s.
Proof.
  induction s; eauto; simpl.
  rewrite IHs; trivial.
Qed.

Lemma N_of_string_of_string_of_N_None s so_far acc
: string_contains_ascii s " " = false
  -> N_of_string_helper s so_far acc = (None, acc ++ s).
Proof.
  revert so_far acc.
  induction s; simpl; trivial; intros;
  repeat match goal with
           | _ => progress cleanup
           | _ => progress simpl in *
           | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
           | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
           | _ => rewrite !string_append_assoc
           | _ => rewrite !string_append_empty
           | _ => rewrite IHs; clear IHs
           | _ => solve [ auto ]
         end.
Qed.

Lemma N_of_string_helper_string_of_Npositive n so_far acc
: N_of_string_helper (string_of_Npositive n) so_far acc = (None, acc ++ string_of_Npositive n).
Proof.
  apply N_of_string_of_string_of_N_None.
  induction n; simpl; rewrite ?string_contains_ascii_append; try rewrite IHn; reflexivity.
Qed.

Lemma N_of_string_of_string_of_N_helper n acc
: N_of_string_helper (string_of_N n) 0 acc = (Some n, "").
Proof.
  revert n.
  repeat match goal with
           | _ => progress simpl in *
           | _ => reflexivity
           | [ |- forall s : string, _ ] => intro
           | [ |- forall n : N, _ ] => intros []
           | [ |- forall p : positive, _ ] => let p := fresh in intro p; induction p
           | _ => rewrite string_append_assoc; progress simpl
           | _ => erewrite N_of_string_append1 by first [ eassumption | apply N_of_string_helper_string_of_Npositive ]
           | _ => erewrite N_of_string_append0 by first [ eassumption | apply N_of_string_helper_string_of_Npositive ]
         end.
Qed.

Lemma N_of_string_of_string_of_N n
: N_of_string (string_of_N n) = (Some n, "").
Proof.
  apply N_of_string_of_string_of_N_helper.
Qed.

Lemma N_of_string_of_string_of_N'' n acc
: N_of_string_helper (string_of_Npositive n ++ " ") 0 acc = (Some (N.pos n), "").
Proof.
  apply (N_of_string_of_string_of_N_helper (N.pos n)).
Qed.

Lemma N_of_string_of_string_of_N' n
: N_of_string (string_of_Npositive n ++ " ") = (Some (N.pos n), "").
Proof.
  apply (N_of_string_of_string_of_N_helper (N.pos n)).
Qed.

Instance Serializable_N : Serializable N
  := {| to_string := string_of_N |}.
Instance Deserializable_N : Deserializable N
  := {| from_string := N_of_string |}.

Instance PrefixSerializable_N {R} `{Reflexive N R} : PrefixSerializable N R
  := {| serialize := _; deserialize := _ |}.
Proof.
  abstract (intros; simpl; rewrite N_of_string_of_string_of_N; split; reflexivity).
  abstract (
      unfold to_string, from_string; simpl; unfold N_of_string;
      intro s1; set (so_far := 0%N); set (acc := ""); generalize so_far; generalize acc; clear; induction s1;
      repeat match goal with
               | _ => progress simpl in *
               | _ => intro
               | _ => progress cleanup
               | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
               | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
               | _ => solve [ eauto ]
             end
    ).
Defined.

Local Opaque Serializable_N.
Local Opaque Deserializable_N.

Existing Instance eq_Reflexive. (* we want this, not [N.divide_reflexive] *)

Definition prod_map {A A' B B'} (f : A -> A') (g : B -> B') : A * B -> A' * B'
  := fun xy => (f (fst xy), g (snd xy)).

Arguments prod_map / .

Instance Serializable_nat : Serializable nat
  := {| to_string x := to_string (N.of_nat x) |}.
Instance Deserializable_nat : Deserializable nat
  := {| from_string x := prod_map (option_map N.to_nat) (fun x => x) (from_string x) |}.

Instance PrefixSerializable_nat {R} `{Reflexive nat R} : PrefixSerializable nat R
  := {| serialize := _; deserialize := _ |}.
Proof.
  abstract (
      intro;
      simpl rewrite (@from_to_string_1_eq N _);
      simpl rewrite (@from_to_string_2 N _ _);
      simpl; rewrite Nnat.Nat2N.id;
      split; reflexivity
    ).
  abstract (
      set (R' := fun a b => R (N.to_nat a) (N.to_nat b));
      assert (Reflexive R') by (repeat intro; hnf; reflexivity);
      simpl; intros s1 s2 x H1;
      pose proof (prefix_closed_1 (R := R') s1 s2 (N.of_nat x)) as H';
      pose proof (prefix_closed_2 (R := R') s1 s2 (N.of_nat x)) as H'';
      repeat match goal with
               | _ => progress simpl in *
               | _ => progress cleanup
               | _ => progress unfold R', option_lift_relation, option_map in *
               | [ H : _ |- _ ] => rewrite !Nnat.Nat2N.id in H
               | [ H : appcontext[match fst (from_string (A := ?A) ?s1) with _ => _ end] |- _ ]
                 => revert H; case_eq (fst (from_string (A := A) s1)); intros
             end
    ).
Defined.

Local Opaque Serializable_nat.
Local Opaque Deserializable_nat.

Lemma leb_xx x : x <=? x = true.
Proof.
  induction x; trivial.
Qed.

Lemma substring_length x : substring 0 (String.length x) x = x.
Proof.
  induction x; trivial; simpl.
  rewrite IHx; trivial.
Qed.

Lemma substring_length' x n : substring (String.length x) n x = "".
Proof.
  induction x; trivial; simpl.
  destruct n; trivial.
Qed.

Lemma string_length_append s1 s2 : String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  revert s2.
  induction s1; simpl; trivial; eauto.
Qed.

Lemma substring_length_append s1 s2 : substring 0 (String.length s1) (s1 ++ s2) = s1.
Proof.
  induction s1; simpl.
  { destruct s2; trivial. }
  { f_equal; eauto. }
Qed.

Fixpoint string_drop n (s : string) : string :=
  match n, s with
    | 0, s => s
    | S n', String _ s' => string_drop n' s'
    | _, "" => ""
  end.

Lemma string_drop_le_append n s1 s2 (H : n <= String.length s1)
: string_drop n (s1 ++ s2) = string_drop n s1 ++ s2.
Proof.
  revert n s2 H.
  induction s1; intros; simpl; trivial.
  { destruct n; simpl; trivial; inversion H. }
  { destruct n; simpl in *; trivial.
    apply le_S_n in H.
    apply IHs1; auto. }
Qed.

Lemma substring_le s s' a b (H : a + b <= String.length s) : substring a b (s ++ s') = substring a b s.
Proof.
  revert a b s' H; induction s; intros; simpl in *.
  { destruct a, b, s'; simpl in *; trivial;
    omega. }
  { repeat match goal with
             | [ |- appcontext[match ?E with _ => _ end] ] => atomic E; destruct E
             | _ => reflexivity
             | _ => progress simpl in *
             | [ H : S _ <= S _ |- _ ] => apply le_S_n in H
           end;
    try (rewrite IHs; clear IHs);
    simpl; trivial. }
Qed.

Instance Serializable_string : Serializable string
  := {| to_string x := to_string (String.length x) ++ x |}.
Instance Deserializable_string : Deserializable string
  := {| from_string x := let nx := from_string (A := nat) x in
                         match fst nx with
                           | Some n => if (n <=? String.length (snd nx))
                                       then (Some (substring 0 n (snd nx)), string_drop n (snd nx))
                                       else (None, x)
                           | None => (None, (snd nx))
                         end |}.

Instance PrefixSerializable_string {R} `{Reflexive string R} : PrefixSerializable string R
  := {| serialize := _; deserialize := _ |}.
Proof.
  abstract (
      intro x; induction x; trivial;
      repeat match goal with
               | [ H : _ |- _ ] => progress rewrite ?substring_length in H |- *
               | [ H : _ |- _ ] => progress rewrite ?substring_length' in H |- *
               | [ H : _ |- _ ] => progress rewrite ?leb_xx in H |- *
               | [ H : _ |- _ ] => simpl rewrite from_to_string_append_1_eq in H
               | [ H : _ |- _ ] => simpl rewrite from_to_string_append_2 in H
               | _ => simpl rewrite from_to_string_append_1_eq
               | _ => simpl rewrite from_to_string_append_2
               | _ => progress simpl in *
               | _ => progress cleanup
             end
    ).
  abstract (
      cbv zeta; intros;
      repeat match goal with
               | [ H : appcontext[match ?E with None => _ | _ => _ end] |- _ ]
                 => (let H' := fresh in
                     case_eq E;
                     [ intros ? H'; rewrite H' in H
                     | intro H'; rewrite H' in H ])
               | _ => (simpl rewrite (@prefix_closed_1_eq _ _ _ _ _); [ | eassumption ])
               | _ => (simpl rewrite (@prefix_closed_2_refl _ _ _ _ _ _ _); [ | eassumption ])
               | _ => progress cleanup
               | _ => rewrite string_length_append
               | _ => progress simpl in *
               | _ => intro
               | [ H : (_ <=? _) = true |- _ ] => apply leb_le in H
               | [ H : appcontext[if ?E then _ else _] |- _ ] => (revert H; case_eq E)
               | [ H : _ <= _ |- _ ] => rewrite (proj2 (@leb_le _ _) (Plus.le_plus_trans _ _ _ H))
               | _ => rewrite substring_le by assumption
               | _ => rewrite string_drop_le_append by assumption
             end
    ).
Defined.

Local Opaque Serializable_string.
Local Opaque Deserializable_string.

Instance Serializable_unit : Serializable unit
  := {| to_string x := "" |}.
Instance Deserializable_unit : Deserializable unit
  := {| from_string s := (Some tt, s) |}.
Instance PrefixSerializable_unit {R} `{Reflexive unit R}
: PrefixSerializable unit R
  := {| serialize := _; deserialize := _ |}.
Proof.
  intros []; split; reflexivity.
  intros ? ? []; split; reflexivity.
Defined.

Instance Serializable_True : Serializable True
  := {| to_string x := "" |}.
Instance Deserializable_True : Deserializable True
  := {| from_string s := (Some I, s) |}.
Instance PrefixSerializable_True {R} `{Reflexive True R}
: PrefixSerializable True R
  := {| serialize := _; deserialize := _ |}.
Proof.
  intros []; split; reflexivity.
  intros ? ? []; split; reflexivity.
Defined.

Instance Serializable_Empty_set : Serializable Empty_set
  := {| to_string x := "" |}.
Instance Deserializable_Empty_set : Deserializable Empty_set
  := {| from_string s := (None, s) |}.
Instance PrefixSerializable_Empty_set {R}
: PrefixSerializable Empty_set R
  := {| serialize := _; deserialize := _ |}.
Proof.
  intros [].
  intros ? ? [].
Defined.


Instance Serializable_False : Serializable False
  := {| to_string x := "" |}.
Instance Deserializable_False : Deserializable False
  := {| from_string s := (None, s) |}.
Instance PrefixSerializable_False {R}
: PrefixSerializable False R
  := {| serialize := _; deserialize := _ |}.
Proof.
  intros [].
  intros ? ? [].
Defined.


Definition Serializable_sum {A B} `{Serializable A, Serializable B} : Serializable (A + B)
  := {| to_string x := match x with
                         | inl x' => "L" ++ to_string x'
                         | inr x' => "R" ++ to_string x'
                       end |}.

Definition Deserializable_sum {A B} `{Deserializable A, Deserializable B} : Deserializable (A + B)
  := {| from_string s := match s with
                           | "" => (None, "")
                           | String a s' => if Ascii.ascii_dec a "L"
                                            then prod_map (option_map (@inl _ _)) id (from_string s')
                                            else if Ascii.ascii_dec a "R"
                                                 then prod_map (option_map (@inr _ _)) id (from_string s')
                                                 else (None, String a s')
                         end |}.

Hint Extern 2 (Deserializable (sum _ _)) => apply Deserializable_sum : typeclass_instances.
Hint Extern 2 (Serializable (sum _ _)) => apply Serializable_sum : typeclass_instances.

Section RelSum.
  Context {A B}
          (RA : relation A) (RB : relation B).

  Definition RelSum : relation (A + B)
    := fun x y => match x, y with
                    | inl x', inl y' => RA x' y'
                    | inr x', inr y' => RB x' y'
                    | _, _ => False
                  end.

  Global Instance RelSum_Reflexive `{Reflexive A RA, Reflexive B RB}
  : Reflexive RelSum.
  Proof. lazy; intros [|]; reflexivity. Qed.

  Global Instance RelSum_Symmetry `{Symmetric A RA, Symmetric B RB}
  : Symmetric RelSum.
  Proof. lazy; intros [|] [|]; auto. Qed.

  Global Instance RelSum_Transitive `{Transitive A RA, Transitive B RB}
  : Transitive RelSum.
  Proof. lazy; intros [|] [|] [|]; eauto; tauto. Qed.
End RelSum.

Definition PrefixSerializable_sum {A B RA RB} `{Reflexive A RA, Reflexive B RB}
           `{PrefixSerializable A RA, PrefixSerializable B RB}
: PrefixSerializable (A + B) (RelSum RA RB).
Proof.
  refine {| serialize := _; deserialize := _ |}.
  abstract (
      intros [x|x]; simpl; rewrite from_to_string_2;
      repeat match goal with
               | _ => progress unfold option_map
               | _ => intro
               | [ R : relation ?A |- appcontext[match fst (from_string (A := ?A) (to_string ?x)) with _ => _ end] ]
                 => (generalize (@from_to_string_1 A R _ x);
                     case_eq (fst (from_string (A := A) (to_string x))))
               | _ => progress simpl in *
               | _ => progress cleanup
             end
    ).
  abstract (
      intros [|a s1] ? [x|x]; simpl; intros;
      repeat match goal with
               | _ => progress cleanup
               | _ => progress simpl in *
               | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
               | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
               | _ => progress unfold option_map in *
               | [ H : appcontext[match ?E with None => _ | _ => _ end] |- _ ]
                 => (revert H; case_eq E; intros)
               | [ |- appcontext[match ?E with None => _ | _ => _ end] ]
                 => (case_eq E; intros)
               | _ => (simpl rewrite (@prefix_closed_1 _ _ _ _ _ _); [ | eassumption ])
               | _ => erewrite prefix_closed_2_refl by eassumption
               | [ H : appcontext[from_string (A := ?A) (?s1 ++ ?s2)] |- _ ]
                 => (let H' := fresh in
                     assert (H' := @prefix_closed_1 A _ _ s1 s2);
                     unfold option_lift_relation in H';
                     cleanup;
                     solve [ eauto ])
             end
    ).
Defined.

Hint Extern 2 (PrefixSerializable (sum _ _) _) => apply PrefixSerializable_sum : typeclass_instances.

Local Opaque Serializable_sum.
Local Opaque Deserializable_sum.

Definition Serializable_option {A} `{Serializable A} : Serializable (option A)
  := {| to_string x := to_string (match x return A + unit with
                                    | Some x' => inl x'
                                    | None => inr tt
                                  end) |}.

Definition Deserializable_option {A} `{Deserializable A} : Deserializable (option A)
  := {| from_string x := let fs := from_string x in
                         (match fst fs with
                            | Some (inl s) => Some (Some s)
                            | Some (inr tt) => Some None
                            | None => None
                          end,
                          snd fs) |}.

Hint Extern 1 (Deserializable (option _)) => apply Deserializable_option : typeclass_instances.
Hint Extern 1 (Serializable (option _)) => apply Serializable_option : typeclass_instances.

Definition PrefixSerializable_option {A RA} `{Reflexive A RA}
           `{PrefixSerializable A RA}
: PrefixSerializable (option A) (option_lift_relation RA).
Proof.
  refine {| serialize := _; deserialize := _ |}.
  abstract (
      intros [x|]; simpl; simpl rewrite (@from_to_string_2 (A + unit) _ _);
      repeat match goal with
               | _ => progress unfold option_lift_relation
               | _ => intro
               | [ |- appcontext[match fst (from_string (A := ?A) (to_string ?x)) with _ => _ end] ]
                 => (generalize (@from_to_string_1 A _ _ x);
                     case_eq (fst (from_string (A := A) (to_string x))))
               | _ => progress destruct_head sum
               | _ => progress simpl in *
               | _ => progress cleanup
             end
    ).
  abstract (
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress simpl in *
               | _ => progress destruct_head option
               | _ => progress destruct_head sum
               | [ |- appcontext[match fst (from_string (A := ?A) ?s) with _ => _ end] ]
                 => case_eq (fst (from_string (A := A) s))
               | [ H : appcontext[match fst (from_string (A := ?A) ?s) with _ => _ end] |- _ ]
                 => case_eq (fst (from_string (A := A) s))
               | [ |- appcontext[from_string (A := ?A) _] ]
                 => (simpl rewrite (@prefix_closed_2_refl A _ _ _ _ _ _); [ | eassumption ])
               | _ => erewrite prefix_closed_2_refl by eassumption
               | [ H : appcontext[from_string (A := ?A) (?s1 ++ ?s2)] |- _ ]
                 => (let H' := fresh in
                     assert (H' := fun x => @prefix_closed_1 A _ _ s1 s2 (inl x));
                     let H'' := fresh in
                     assert (H'' := fun x => @prefix_closed_1 A _ _ s1 s2 (inr x));
                     unfold option_lift_relation, RelSum in H', H'';
                     simpl in *;
                       cleanup;
                     solve [ eauto ])
             end
    ).
Defined.

Hint Extern 1 (PrefixSerializable (option _) _) => apply PrefixSerializable_option : typeclass_instances.

Local Opaque Serializable_option.
Local Opaque Deserializable_option.

Definition Serializable_prod {A B} `{Serializable A, Serializable B}
: Serializable (A * B)
  := {| to_string x := to_string (fst x) ++ to_string (snd x) |}.

Definition Deserializable_prod {A B} `{Deserializable A, Deserializable B}
: Deserializable (A * B)
  := {| from_string x := let fs := from_string x in
                         let fs' := from_string (snd fs) in
                         match fst fs, fst fs' with
                           | Some a, Some b => (Some (a, b), snd fs')
                           | _, _ => (None, x)
                         end |}.

Hint Extern 2 (Deserializable (prod _ _)) => apply Deserializable_prod : typeclass_instances.
Hint Extern 2 (Serializable (prod _ _)) => apply Serializable_prod : typeclass_instances.

Definition PrefixSerializable_prod {A B RA RB}
           `{Reflexive A RA, Reflexive B RB}
           `{PrefixSerializable A RA, PrefixSerializable B RB}
: PrefixSerializable (A * B) (RelProd RA RB).
Proof.
  refine {| serialize := _; deserialize := _ |}.
  abstract (
      repeat match goal with
               | _ => progress unfold option_lift_relation
               | _ => intro
               | _ => progress destruct_head prod
               | _ => progress unfold RelProd, relation_conjunction, predicate_intersection in *
               | _ => progress simpl in *
               | _ => progress cleanup
               | _ => rewrite from_to_string_append_2
               | _ => rewrite from_to_string_2
               | [ |- appcontext[match fst (from_string (A := ?A) (to_string ?x ++ ?y)) with _ => _ end] ]
                 => (generalize (@from_to_string_append_1 A _ _ x y);
                     case_eq (fst (from_string (A := A) (to_string x ++ y))))
               | [ |- appcontext[match fst (from_string (A := ?A) (to_string ?x)) with _ => _ end] ]
                 => (generalize (@from_to_string_1 A _ _ x);
                     case_eq (fst (from_string (A := A) (to_string x))))

             end
    ).
  abstract (
      simpl; intros s1 s2;
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress simpl in *
               | _ => progress unfold RelProd, RelCompFun, relation_conjunction, predicate_intersection, option_lift_relation in *
               | _ => erewrite prefix_closed_2_refl by eassumption
               | [ H : _ |- _ ] => erewrite prefix_closed_2_refl in H by eassumption
               | [ |- appcontext[match fst (from_string (A := ?A) ?s) with _ => _ end] ]
                 => (case_eq (fst (from_string (A := A) s)))
               | [ H : appcontext[match fst (from_string (A := ?A) ?s) with _ => _ end] |- _ ]
                 => (revert H; case_eq (fst (from_string (A := A) s)))
               | [ H : appcontext[from_string (A := ?A) (?s1 ++ ?s2)] |- _ ]
                 => (let H' := fresh in
                     assert (H' := @prefix_closed_1 A _ _ s1 s2);
                     unfold option_lift_relation in H';
                     simpl in *;
                       cleanup;
                     solve [ eauto
                           | exfalso; eauto ])
             end).
Defined.

Hint Extern 2 (PrefixSerializable (prod _ _) _) => apply PrefixSerializable_prod : typeclass_instances.

Local Opaque Serializable_prod.
Local Opaque Deserializable_prod.

Fixpoint list_to_string_helper {A} `{Serializable A} (ls : list A) : string :=
  match ls with
    | nil => ""
    | x::xs => to_string x ++ list_to_string_helper xs
  end.

Definition list_to_string {A} `{Serializable A} (ls : list A) : string :=
  to_string (List.length ls) ++ list_to_string_helper ls.

Fixpoint list_from_string_helper {A} `{Deserializable A} n (s : string) : option (list A) * string :=
  match n with
    | 0 => (Some nil, s)
    | S n' => let fs := from_string s in
              let fs' := list_from_string_helper n' (snd fs) in
              match fst fs, fst fs' with
                | Some x, Some xs => (Some (x::xs), snd fs')
                | _, _ => (None, s)
              end
  end.

Lemma list_from_string_helper_append_1 {A R} `{Reflexive A R}
      `{PrefixSerializable A R} n (s1 s2 : string) x
: option_lift_relation (eqlistA R) (fst (list_from_string_helper n s1)) (Some x)
  -> option_lift_relation (eqlistA R) (fst (list_from_string_helper n (s1 ++ s2))) (Some x).
Proof.
  revert s1 s2 x.
  induction n;
    intro s1;
    case_eq (fst (from_string (A := A) s1));
    repeat match goal with
             | _ => intro
             | _ => progress cleanup
             | _ => progress simpl in *
             | _ => erewrite prefix_closed_2_refl by eassumption
             | [ |- appcontext[fst (list_from_string_helper _ (?s1 ++ ?s2))] ]
               => specialize (IHn s1 s2)
             | _ => progress unfold option_lift_relation in *
             | _ => erewrite prefix_closed by eassumption
             | [ H : appcontext[match ?E with None => _ | _ => _ end] |- _ ]
               => (revert H; case_eq E)
             | [ |- appcontext[match ?E with None => _ | _ => _ end] ]
               => case_eq E
             | _ => erewrite IHn by eassumption
             | [ H : fst (from_string (A := ?A) (?s1 ++ ?s2)) = _ |- _ ]
               => (pose proof (@prefix_closed_1 A _ _ s1 s2);
                   simpl in *; cleanup;
                   simpl in *;
                     solve [ eauto ])
           end.
Qed.

Instance eqlistA_Reflexive {A R} `{Reflexive A R} : Reflexive (eqlistA R).
Proof.
  intro ls; induction ls; constructor; auto.
Qed.

Instance eqlistA_Symmetric {A R} `{Symmetric A R} : Symmetric (eqlistA R).
Proof.
  intro ls; induction ls; intros ls' H'; inversion H'; subst; constructor;
  eauto.
Qed.

Instance eqlistA_Transitive {A R} `{Transitive A R} : Transitive (eqlistA R).
Proof.
  intro ls; induction ls; intros ls' ls'' H' H'';
  inversion H'; subst; inversion H'';
  subst; try constructor;
  eauto;
  try congruence.
Qed.

Lemma list_from_string_helper_append_2 {A R} `{Reflexive A R}
      `{PrefixSerializable A R} n (s1 s2 : string) x
: option_lift_relation (eqlistA R) (fst (list_from_string_helper n s1)) (Some x)
  -> snd (list_from_string_helper (A := A) n (s1 ++ s2)) = snd (list_from_string_helper (A := A) n s1) ++ s2.
Proof.
  revert s1 s2 x; induction n;
  repeat match goal with
           | _ => intro
           | _ => progress cleanup
           | _ => progress simpl in *
           | [ H : _ |- _ ] => erewrite prefix_closed_2_refl in H by eassumption
           | _ => erewrite prefix_closed_2_refl by eassumption
           | [ H : appcontext[match ?E with None => _ | _ => _ end] |- _ ]
             => (revert H; case_eq E)
           | [ |- appcontext[match ?E with None => _ | _ => _ end] ]
             => case_eq E
           | _ => erewrite IHn
           | [ H : fst (from_string (A := ?A) (?s1 ++ ?s2)) = _ |- _ ]
             => (pose proof (@prefix_closed_1 A _ _ s1 s2);
                 simpl in *; cleanup;
                 simpl in *;
                   solve [ eauto ])
           | [ H : fst (list_from_string_helper (A := ?A) ?n (?s1 ++ ?s2)) = None |- _ ]
             => (pose proof (@list_from_string_helper_append_1 A _ _ _ n s1 s2);
                 simpl in *; cleanup;
                 simpl in *; cleanup;
                 solve [ exfalso; eauto ])
           | [ H : fst (from_string (A := ?A) (?s1 ++ ?s2)) = None |- _ ]
             => (pose proof (@prefix_closed_1 A _ _ s1 s2);
                 simpl in *; cleanup;
                 simpl in *; cleanup;
                 solve [ exfalso; eauto ])
           | [ H : _ |- _ ] => rewrite H; reflexivity
         end.
Qed.

Definition list_from_string {A} `{Deserializable A} (s : string) : option (list A) * string :=
  let fs := from_string (A := nat) s in
  match fst fs with
    | Some n => list_from_string_helper n (snd fs)
    | None => (None, s)
  end.

Arguments list_from_string / .
Arguments list_to_string / .

Definition Serializable_list {A} `{Serializable A} : Serializable (list A)
  := {| to_string x := list_to_string x |}.

Definition Deserializable_list {A} `{Deserializable A} : Deserializable (list A)
  := {| from_string x := list_from_string x |}.

Hint Extern 1 (Deserializable (list _)) => apply Deserializable_list : typeclass_instances.
Hint Extern 1 (Serializable (list _)) => apply Serializable_list : typeclass_instances.

Definition PrefixSerializable_list {A R} `{Reflexive A R}
           `{PrefixSerializable A R}
: PrefixSerializable (list A) (eqlistA R).
Proof.
  refine {| serialize := _ |}.
  unfold to_string, from_string; simpl; unfold list_from_string, list_to_string.
  abstract (
      intro x; induction x; trivial;
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | [ H : _ |- _ ] => simpl rewrite (@from_to_string_append_1_eq nat _) in H
               | [ H : _ |- _ ] => simpl rewrite (@from_to_string_append_2 nat _ _) in H
               | _ => progress simpl in *
               | _ => progress unfold option_lift_relation in *
               | [ H : _ |- _ ] => (rewrite H; reflexivity)
               | [ |- appcontext[match fst (from_string (A := ?A) (to_string ?x ++ ?y)) with _ => _ end] ]
                 => (generalize (@from_to_string_append_1 A _ _ x y);
                     case_eq (fst (from_string (A := A) (to_string x ++ y))))
               | [ |- appcontext[match fst (from_string (A := ?A) (to_string ?x)) with _ => _ end] ]
                 => (generalize (@from_to_string_1 A _ _ x);
                     case_eq (fst (from_string (A := A) (to_string x))))
               | [ |- appcontext[snd (from_string (A := ?A) (to_string ?x ++ ?y))] ]
                 => simpl rewrite (@from_to_string_append_2 A _ _)
               | [ H : appcontext[match ?E with None => _ | _ => _ end] |- _ ]
                 => (revert H; case_eq E)
               | _ => solve [ eauto ]
             end
    ).
  unfold to_string, from_string; simpl; unfold list_from_string, list_to_string.
  abstract (
      intro s1;
      case_eq (fst (from_string (A := nat) s1));
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress simpl in *
               | [ H : appcontext[from_string (A := ?A) _] |- _ ]
                 => (simpl rewrite (@prefix_closed_2_refl A _ _ _ _ _ _) in H; [ | eassumption ])
               | [ H : _ |- _ ] => erewrite prefix_closed_2_refl in H by eassumption
               | [ H : _ |- _ ] => simpl rewrite (@prefix_closed_1_eq nat _ _ _ _) in H; [ | eassumption ]
               | _ => erewrite prefix_closed_2_refl by eassumption
               | _ => simpl rewrite (@prefix_closed_2_refl nat _ _ _ _ _ _); [ | eassumption ]
               | _ => apply list_from_string_helper_append
               | _ => progress unfold option_lift_relation in *
               | [ H : appcontext[match ?E with None => _ | _ => _ end] |- _ ]
                 => (revert H; case_eq E)
               | [ |- appcontext[match ?E with None => _ | _ => _ end] ]
                 => (revert H; case_eq E)
               | [ H : fst (list_from_string_helper (A := ?A) ?n (?s0 ++ ?s1)) = _ |- _ ]
                 => (pose proof (@list_from_string_helper_append_1 A _ _ _ n s0 s1);
                     simpl in *; cleanup;
                     simpl in *; solve [ eauto ])
               | [ |- _ ] => eapply list_from_string_helper_append_2
               | [ H : _ |- _ ] => rewrite H; reflexivity
             end
    ).
Defined.

Hint Extern 1 (PrefixSerializable (list _) _) => apply PrefixSerializable_list : typeclass_instances.

Local Opaque Serializable_list.
Local Opaque Deserializable_list.
