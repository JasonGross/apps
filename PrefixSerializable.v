Require Import Coq.Strings.String Coq.Numbers.Natural.Peano.NPeano Coq.NArith.BinNat Coq.omega.Omega.
Require Export PrefixSerializableDefinitions.
Require Import Common.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope string_scope.

Lemma from_to_string_append {A} `{PrefixSerializable A} x s : from_string (to_string x ++ s) = (Some x, s).
Proof.
  erewrite prefix_closed; try rewrite from_to_string; reflexivity.
Qed.

Local Arguments Ascii.ascii_dec !_ !_ / .

Instance PrefixSerializable_bool : PrefixSerializable bool
  := {| serialize := {| to_string b := if b : bool then "1" else "0" |};
        deserialize := {| from_string x := match x with
                                             | "" => (None, "")
                                             | String a s' => if Ascii.ascii_dec a "1"
                                                              then (Some true, s')
                                                              else if Ascii.ascii_dec a "0"
                                                                   then (Some false, s')
                                                                   else (None, x)
                                           end |} |}.
Proof.
  intros []; reflexivity.
  abstract (
      intro s1; induction s1; intros;
      repeat match goal with
               | _ => reflexivity
               | [ b : bool |- _ ] => destruct b
               | _ => progress simpl in *
               | _ => progress unfold from_string, to_string in *
               | _ => progress subst
               | [ H : None = Some _ |- _ ] => solve [ inversion H ]
               | [ H : false = true |- _ ] => solve [ inversion H ]
               | [ H : true = false |- _ ] => solve [ inversion H ]
               | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
               | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
               | [ |- appcontext[prefix _ ?s] ] => (atomic s; destruct s)
               | [ H : appcontext[prefix _ ?s] |- _ ] => (atomic s; destruct s)
               | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
               | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
             end
    ).
Defined.

Local Opaque PrefixSerializable_bool.

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
           | _ => reflexivity
           | _ => progress subst
           | _ => intro
           | [ H : None = Some _ |- _ ] => solve [ inversion H ]
           | [ H : Some _ = None |- _ ] => solve [ inversion H ]
           | [ H : false = true |- _ ] => solve [ inversion H ]
           | [ H : true = false |- _ ] => solve [ inversion H ]
           | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
           | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
           | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
           | [ H : _ |- _ ] => rewrite H by assumption
           | [ |- appcontext[match ?E with _ => _ end] ] => atomic E; destruct E
           | [ |- Some _ = Some _ ] => apply f_equal
           | [ |- (_, _) = (_, _) ] => apply f_equal2
           | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
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
           | _ => reflexivity
           | _ => progress simpl in *
           | _ => progress subst
           | [ H : false = true |- _ ] => solve [ inversion H ]
           | [ H : true = false |- _ ] => solve [ inversion H ]
           | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
           | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
           | [ |- (_, _) = (_, _) ] => apply f_equal2
           | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
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

Lemma N_of_string_of_string_of_N n acc
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

Lemma N_of_string_of_string_of_N'' n acc
: N_of_string_helper (string_of_Npositive n ++ " ") 0 acc = (Some (N.pos n), "").
Proof.
  apply (N_of_string_of_string_of_N (N.pos n)).
Qed.

Lemma N_of_string_of_string_of_N' n
: N_of_string (string_of_Npositive n ++ " ") = (Some (N.pos n), "").
Proof.
  apply (N_of_string_of_string_of_N (N.pos n)).
Qed.

Instance PrefixSerializable_N : PrefixSerializable N
  := {| serialize := {| to_string := string_of_N |};
        deserialize := {| from_string := N_of_string |} |}.
Proof.
  intros; apply N_of_string_of_string_of_N.
  abstract (
      unfold to_string, from_string, N_of_string;
      intro s1; set (so_far := 0%N); set (acc := ""); generalize so_far; generalize acc; clear; induction s1;
      repeat match goal with
               | _ => progress simpl in *
               | _ => intro
               | _ => progress subst
               | _ => assumption
               | [ H : None = Some _ |- _ ] => solve [ inversion H ]
               | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
               | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
               | [ |- (_, _) = (_, _) ] => apply f_equal2
               | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
               | _ => solve [ eauto ]
             end
    ).
Defined.

Local Opaque PrefixSerializable_N.

Definition prod_map {A A' B B'} (f : A -> A') (g : B -> B') : A * B -> A' * B'
  := fun xy => (f (fst xy), g (snd xy)).

Arguments prod_map / .

Instance PrefixSerializable_nat : PrefixSerializable nat
  := {| serialize := {| to_string x := to_string (N.of_nat x) |};
        deserialize := {| from_string x := prod_map (option_map N.to_nat) (fun x => x) (from_string x) |} |}.
Proof.
  abstract (intro; simpl rewrite (@from_to_string N _); simpl; rewrite Nnat.Nat2N.id; reflexivity).
  abstract (
      intros; simpl prod_map in *; cbv beta in *; apply injective_projections; simpl;
      [
      | match goal with
          | [ H : appcontext[from_string ?s1] |- _ ] => atomic s1; revert H; case_eq (from_string s1); intros
        end;
        match goal with
          | [ H : option _ |- _ ] => destruct H
        end ];
      let x := match goal with x : nat |- _ => constr:x end in
      rewrite prefix_closed with (x0 := N.of_nat x);
      solve [ repeat match goal with
                       | _ => reflexivity
                       | _ => eassumption
                       | [ H : context[from_string ?s] |- context[from_string ?s] ] => destruct (from_string s)
                       | _ => progress simpl in *
                       | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
                       | [ |- Some _ = Some _ ] => apply f_equal
                       | [ H : None = Some _ |- _ ] => solve [ inversion H ]
                       | _ => progress subst
                       | [ |- (_, _) = (_, _) ] => apply f_equal2
                       | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
                       | _ => rewrite !Nnat.Nat2N.id
                       | _ => rewrite !Nnat.N2Nat.id
                       | _ => progress destruct_head option
                     end ]
    ).
Defined.

Local Opaque PrefixSerializable_nat.

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

Instance PrefixSerializable_string : PrefixSerializable string
  := {| serialize := {| to_string x := to_string (String.length x) ++ x |};
        deserialize := {| from_string x := let nx := from_string (A := nat) x in
                                           match fst nx with
                                             | Some n => if (n <=? String.length (snd nx))
                                                         then (Some (substring 0 n (snd nx)), string_drop n (snd nx))
                                                         else (None, x)
                                             | None => (None, (snd nx))
                                           end |} |}.
Proof.
  abstract (
      intro x; induction x; trivial;
      repeat match goal with
               | [ H : _ |- _ ] => progress rewrite ?substring_length in H |- *
               | [ H : _ |- _ ] => progress rewrite ?substring_length' in H |- *
               | [ H : _ |- _ ] => progress rewrite ?from_to_string_append in H |- *
               | [ H : _ |- _ ] => progress rewrite ?leb_xx in H |- *
               | _ => progress simpl in *
               | _ => progress change (@serialize) with (fun A x => @to_string A _)
               | _ => progress unfold from_string, to_string in *
               | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
               | [ |- Some _ = Some _ ] => apply f_equal
               | _ => progress subst
               | [ |- (_, _) = (_, _) ] => apply f_equal2
               | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
               | _ => reflexivity
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
               | _ => erewrite prefix_closed by eassumption
               | _ => reflexivity
               | _ => rewrite string_length_append
               | _ => progress simpl in *
               | _ => intro
               | [ H : Some _ = None |- _ ] => solve [ inversion H ]
               | [ H : None = Some _ |- _ ] => solve [ inversion H ]
               | [ H : (_ <=? _) = true |- _ ] => apply leb_le in H
               | [ H : appcontext[if ?E then _ else _] |- _ ] => (revert H; case_eq E)
               | [ H : _ <= _ |- _ ] => rewrite (proj2 (@leb_le _ _) (Plus.le_plus_trans _ _ _ H))
               | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
               | [ |- Some _ = Some _ ] => apply f_equal
               | _ => progress subst
               | [ |- (_, _) = (_, _) ] => apply f_equal2
               | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
               | _ => rewrite substring_le by assumption
               | _ => rewrite string_drop_le_append by assumption
             end
    ).
Defined.

Local Opaque PrefixSerializable_string.

Instance PrefixSerializable_unit : PrefixSerializable unit
  := {| serialize := {| to_string x := "" |};
        deserialize := {| from_string s := (Some tt, s) |} |}.
Proof.
  intros []; reflexivity.
  intros ? ? []; reflexivity.
Defined.

Instance PrefixSerializable_True : PrefixSerializable True
  := {| serialize := {| to_string x := "" |};
        deserialize := {| from_string s := (Some I, s) |} |}.
Proof.
  intros []; reflexivity.
  intros ? ? []; reflexivity.
Defined.

Instance PrefixSerializable_Empty : PrefixSerializable Empty_set
  := {| serialize := {| to_string x := "" |};
        deserialize := {| from_string s := (None, s) |} |}.
Proof.
  intros [].
  intros ? ? [].
Defined.

Instance PrefixSerializable_False : PrefixSerializable False
  := {| serialize := {| to_string x := "" |};
        deserialize := {| from_string s := (None, s) |} |}.
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

Definition PrefixSerializable_sum {A B} `{PrefixSerializable A, PrefixSerializable B} : PrefixSerializable (A + B).
Proof.
  refine {| serialize := _; deserialize := _ |}.
  abstract (intros [x|x]; simpl; rewrite from_to_string; simpl; trivial).
  abstract (
      intros [|a s1] ? [x|x]; simpl; intros;
      repeat match goal with
               | [ H : None = Some _ |- _ ] => solve [ inversion H ]
               | _ => progress subst
               | _ => reflexivity
               | _ => progress simpl in *
               | [ |- (_, _) = (_, _) ] => apply f_equal2
               | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
               | [ H : inl _ = inl _ |- _ ] => (inversion H; clear H)
               | [ H : inr _ = inr _ |- _ ] => (inversion H; clear H)
               | [ |- appcontext[Ascii.ascii_dec ?a ?b] ] => destruct (Ascii.ascii_dec a b)
               | [ H : appcontext[Ascii.ascii_dec ?a ?b] |- _ ] => destruct (Ascii.ascii_dec a b)
               | _ => progress unfold option_map in *
               | [ H : appcontext[match ?E with None => _ | _ => _ end] |- _ ]
                 => (let H' := fresh in
                     case_eq E;
                     [ intros ? H'; rewrite H' in H
                     | intro H'; rewrite H' in H ])
               | _ => erewrite prefix_closed by eassumption
             end
    ).
Defined.

Hint Extern 2 (PrefixSerializable (sum _ _)) => apply PrefixSerializable_sum : typeclass_instances.

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

Definition PrefixSerializable_option {A} `{PrefixSerializable A} : PrefixSerializable (option A).
Proof.
  refine {| serialize := _; deserialize := _ |}.
  abstract (intro; simpl rewrite (@from_to_string (A + unit) _); destruct_head option; trivial).
  abstract (
      intro s1; cbv zeta; case_eq (fst (from_string (A := A + unit) s1)); [ intros [?|?] | ];
      repeat match goal with
               | _ => intro
               | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
               | _ => progress subst
               | _ => progress simpl in *
               | [ H : ?x = Some _, H' : appcontext[match ?x with _ => _ end] |- _ ] => rewrite H in H'
               | [ H : ?x = None, H' : appcontext[match ?x with _ => _ end] |- _ ] => rewrite H in H'
               | [ H : None = Some _ |- _ ] => solve [ inversion H ]
               | _ => reflexivity
               | _ => progress destruct_head unit
               | _ => let H := fresh in
                      pose proof (@prefix_closed (A + unit) _) as H;
                        simpl in H |- *;
                          erewrite H by eassumption
             end
    ).
Defined.

Hint Extern 1 (PrefixSerializable (option _)) => apply PrefixSerializable_option : typeclass_instances.

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

Definition PrefixSerializable_prod {A B} `{PrefixSerializable A, PrefixSerializable B}
: PrefixSerializable (A * B).
Proof.
  refine {| serialize := _; deserialize := _ |}.
  abstract (intros [??]; simpl rewrite (@from_to_string_append A _); simpl; rewrite from_to_string; simpl; trivial).
  abstract (
      simpl; intro s1;
      case_eq (fst (from_string (A := A) s1)); simpl;
      case_eq (fst (from_string (A := B) (snd (from_string (A := A) s1)))); simpl;
      repeat match goal with
               | _ => intro
               | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
               | _ => progress subst
               | _ => progress simpl in *
               | [ H : None = Some _ |- _ ] => solve [ inversion H ]
               | _ => reflexivity
               | _ => progress destruct_head unit
               | _ => erewrite prefix_closed by eassumption
             end
    ).
Defined.

Hint Extern 2 (PrefixSerializable (prod _ _)) => apply PrefixSerializable_prod : typeclass_instances.

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

Lemma list_from_string_helper_append {A} `{PrefixSerializable A} n (s1 s2 : string) x
: fst (list_from_string_helper n s1) = Some x
  -> list_from_string_helper n (s1 ++ s2) = (Some x, snd (list_from_string_helper n s1) ++ s2).
Proof.
  revert s1 s2 x.
  induction n;
    intro s1;
    case_eq (fst (from_string (A := A) s1));
    repeat match goal with
             | _ => intro
             | _ => reflexivity
             | _ => progress simpl in *
             | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
             | _ => progress subst
             | _ => erewrite prefix_closed by eassumption
             | [ H : ?a = Some _, H' : appcontext[?a] |- _ ] => rewrite H in H'
             | [ H : ?a = Some _ |- appcontext[?a] ] => rewrite H
             | [ H : None = Some _ |- _ ] => solve [ inversion H ]
             | [ H : appcontext[match ?E with None => _ | _ => _ end] |- _ ]
               => (let H' := fresh in
                   case_eq E;
                   [ intros ? H'; rewrite H' in H
                   | intro H'; rewrite H' in H ])
             | _ => erewrite IHn by eassumption
             | [ |- (_, _) = (_, _) ] => apply f_equal2
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

Definition PrefixSerializable_list {A} `{PrefixSerializable A} : PrefixSerializable (list A).
Proof.
  refine {| serialize := _ |}.
  unfold to_string, from_string; simpl; unfold list_from_string, list_to_string.
  abstract (
      intro x; induction x; trivial;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite from_to_string_append in H
               | _ => rewrite from_to_string_append
               | _ => progress simpl in *
               | [ H : _ |- _ ] => rewrite H; reflexivity
             end
    ).
  unfold to_string, from_string; simpl; unfold list_from_string, list_to_string.
  abstract (
      intro s1;
      case_eq (fst (from_string (A := nat) s1));
      repeat match goal with
               | _ => intro
               | [ H : Some _ = Some _ |- _ ] => (inversion H; clear H)
               | _ => progress subst
               | _ => progress simpl in *
               | [ H : None = Some _ |- _ ] => solve [ inversion H ]
               | _ => reflexivity
               | _ => assumption
               | _ => progress destruct_head unit
               | _ => erewrite prefix_closed by eassumption
               | _ => apply list_from_string_helper_append
             end
    ).
Defined.

Hint Extern 1 (PrefixSerializable (list _)) => apply PrefixSerializable_list : typeclass_instances.

Local Opaque Serializable_list.
Local Opaque Deserializable_list.
