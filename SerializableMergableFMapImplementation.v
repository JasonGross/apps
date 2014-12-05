Require Import Coq.Strings.String Coq.FSets.FMapInterface.
Require Import SerializableMergableFMapInterface PrefixSerializable.
Require Import Common.

Local Open Scope bool_scope.
Set Implicit Arguments.

Module MakeSerializableMergableMap (E : SerializableOrderedType) (M : Sfun E) <: SerializableMergableMapInterface E.
  Definition key := M.key.
  Definition t elt := M.t (nat * option elt).

  Local Ltac add_facts :=
    repeat match goal with
             | _ => progress subst
             | [ H : Some _ = None |- _ ] => solve [ inversion H ]
             | [ H : None = Some _ |- _ ] => solve [ inversion H ]
             | [ H : E.eq ?x ?y, H' : M.MapsTo ?x ?e ?m |- _ ]
               => unique pose proof (M.MapsTo_1 H H')
             | [ H : E.eq ?x ?y |- _ ]
               => unique pose proof (E.eq_sym H)
             | [ x : key |- _ ]
               => unique pose proof (E.eq_refl x)
             | [ H : E.eq ?x ?y, H' : E.eq ?y ?z |- _ ]
               => unique pose proof (E.eq_trans H H')
             | [ H : E.eq ?x ?y, H' : context[M.add ?x ?e ?m] |- _ ]
               => unique pose proof (M.add_1 m e H)
             | [ H : M.MapsTo ?x ?e ?m |- _ ]
               => unique pose proof (M.find_1 H)
             | [ H : M.find ?x ?m = Some ?e |- _ ]
               => unique pose proof (M.find_2 H)
             | [ H : ?a = ?b |- _ ]
               => unique pose proof (Logic.eq_sym H)
             | [ H : ?a = ?b, H' : ?b = ?c |- _ ]
               => unique pose proof (Logic.eq_trans H H')
             | [ H : Some ?x = Some ?y |- _ ]
               => unique pose proof (Some_inj H)
             | [ H : (?x, ?y) = (?x', ?y') :> _ * _ |- _ ]
               => unique pose proof (f_equal (@fst _ _) H : x = x')
             | [ H : (?x, ?y) = (?x', ?y') :> _ * _ |- _ ]
               => unique pose proof (f_equal (@snd _ _) H : y = y')
             | [ H : ~E.eq ?x ?y |- _ ]
               => unique pose proof ((fun H' => H (E.eq_sym H')) : ~E.eq y x)
             | [ H : ~E.eq ?x ?y, H' : M.MapsTo ?y ?e (M.add ?x ?e' ?m) |- _ ]
               => unique pose proof (M.add_3 H H')
             | [ H : ~E.eq ?x ?y, H' : M.MapsTo ?y ?e ?m, H'' : appcontext[M.add ?x ?e' ?m] |- _ ]
               => unique pose proof (M.add_2 e' H H')
             | [ H : ~E.eq ?x ?y, H' : M.MapsTo ?y ?e ?m |- appcontext[M.add ?x ?e' ?m] ]
               => unique pose proof (M.add_2 e' H H')
           end.

  Section elt.
    Variable elt : Type.

    Definition empty := M.empty (nat * option elt).
    Definition is_empty (m : t elt) :=
      M.fold (fun k v b => b && match snd v with None => true | Some _ => false end)
             m
             true.
    Definition add (k : key) (v : elt) (m : t elt) : t elt
      := M.add k
               (match M.find k m with
                  | Some (gen, v0) => S gen
                  | None => 0
                end,
                Some v)
               m.

    Definition find (k : key) (m : t elt) : option elt
      := match M.find k m with
           | Some (_, Some v) => Some v
           | _ => None
         end.

    Definition remove (k : key) (m : t elt) : t elt
      := match M.find k m with
           | Some (gen, v0) => M.add k (S gen, None) m
           | None => m
         end.

    Definition mem (k : key) (m : t elt) : bool
      := match M.find k m with
           | Some (_, Some _) => true
           | _ => false
         end.

    Variable elt' elt'' : Type.

    Definition map (f : elt -> elt') (m : t elt) : t elt'
      := M.map (fun v => (fst v, option_map f (snd v))) m.

    Definition mapi (f : key -> elt -> elt') (m : t elt) : t elt'
      := M.mapi (fun k v => (fst v, option_map (f k) (snd v))) m.

    Definition map2 (f : option elt -> option elt' -> option elt'') (m : t elt) (m' : t elt') : t elt''
      := M.map2 (fun v1 v2 =>
                   match v1, v2 with
                     | Some (gen1, v1'), Some (gen2, v2') => option_map (pair (max gen1 gen2)) (option_map Some (f v1' v2'))
                     | Some (gen1, v1'), None => option_map (pair gen1) (option_map Some (f v1' None))
                     | None, Some (gen2, v2') => option_map (pair gen2) (option_map Some (f None v2'))
                     | None, None => option_map (pair 0) (option_map Some (f None None))
                   end)
                m m'.

    Fixpoint filter_some {A B} (ls : list (A * option B)) : list (A * B)
      := match ls with
           | nil => nil
           | (a, Some b)::ls' => (a, b)::filter_some ls'
           | (a, None)::ls' => filter_some ls'
         end.

    Local Ltac InA_filter_some_t :=
      repeat match goal with
               | _ => intro
               | _ => progress subst
               | _ => progress simpl in *
               | _ => progress destruct_head prod
               | _ => progress destruct_head option
               | _ => assumption
               | [ H : InA _ _ nil |- _ ] => solve [ inversion H ]
               | [ H : InA _ _ (_::_) |- _ ] => inversion H; clear H
               | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
               | _ => progress unfold not in *
               | _ => solve [ left; eauto ]
               | _ => solve [ right; eauto ]
               | _ => solve [ exfalso; eauto ]
             end.

    Lemma InA_filter_some1 {A B} (eqP : forall B', A * B' -> A * B' -> Prop)
          (H : forall a a' b b', eqP B (a, b) (a', b') -> eqP _ (a, Some b) (a', Some b'))
          ls (a : A) (b : B)
    : InA (@eqP B) (a, b) (filter_some ls)
      -> InA (eqP (option B)) (a, Some b) ls.
    Proof.
      induction ls; InA_filter_some_t.
    Qed.

    Lemma InA_filter_some2 {A B} (eqP : forall B', A * B' -> A * B' -> Prop)
          (H : forall a a' b b', eqP _ (a, Some b) (a', Some b') -> eqP B (a, b) (a', b'))
          (H1 : forall a a' (b : B), ~eqP _ (a, Some b) (a', None))
          ls (a : A) (b : B)
    : InA (eqP (option B)) (a, Some b) ls
      -> InA (@eqP B) (a, b) (filter_some ls).
    Proof.
      induction ls; InA_filter_some_t.
    Qed.

    Lemma InA_filter_some {A B} (eqP : forall B', A * B' -> A * B' -> Prop)
          (H : forall a a' b b', eqP _ (a, Some b) (a', Some b') <-> eqP B (a, b) (a', b'))
          (H1 : forall a a' (b : B), ~eqP _ (a, Some b) (a', None))
          ls (a : A) (b : B)
    : InA (@eqP B) (a, b) (filter_some ls)
      <-> InA (eqP (option B)) (a, Some b) ls.
    Proof.
      split;
      [ eapply InA_filter_some1
      | eapply InA_filter_some2 ];
      split_iff;
      eauto.
    Qed.

    Lemma InA_filter_some_fst {A B} (eqP : relation A)
          ls (a : A) (b : B)
    : InA (fun p p' => eqP (fst p) (fst p')) (a, b) (filter_some ls)
      -> InA (fun p p' => eqP (fst p) (fst p')) (a, Some b) ls.
    Proof.
      apply (@InA_filter_some1 _ _(fun _ p p' => eqP (fst p) (fst p'))); simpl; trivial.
    Qed.

    Lemma NoDupA_filter_some {A B} (f : relation A) (ls : list (A * option B))
    : NoDupA (fun p p' => f (fst p) (fst p')) ls
      -> NoDupA (fun p p' => f (fst p) (fst p')) (filter_some ls).
    Proof.
      induction ls;
      repeat match goal with
               | _ => intro
               | _ => progress simpl in *
               | _ => progress subst
               | _ => assumption
               | [ |- _ <-> _ ] => split
               | [ H : NoDupA _ (_::_) |- _ ] => (inversion H; clear H)
               | [ |- NoDupA _ nil ] => constructor
               | [ |- NoDupA _ (_::_) ] => constructor
               | _ => progress destruct_head prod
               | _ => progress destruct_head option
               | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
               | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
               | [ H : InA _ _ (filter_some _) |- _ ] => unique pose proof (@InA_filter_some_fst _ _ _ _ _ _ H)
               | _ => progress unfold not in *
               | _ => solve [ eauto ]
             end.
    Qed.

    Section InA_map.
      Context {A B}
              (eqPA : A -> A -> Prop)
              (eqPB : B -> B -> Prop)
              (f : A -> B).

      Lemma InA_map1 x0 x1 ls
            (H0 : forall a, eqPA x0 a -> eqPB x1 (f a))
      : InA eqPA x0 ls -> InA eqPB x1 (List.map f ls).
      Proof.
        induction ls as [|?? IHls]; intro H; inversion H; subst; simpl;
        solve [ left; apply H0; assumption
              | right; apply IHls; assumption ].
      Qed.

      Lemma InA_map2 x0 x1 ls
            (H0 : forall a, eqPB x1 (f a) -> eqPA x0 a)
      : InA eqPB x1 (List.map f ls) -> InA eqPA x0 ls.
      Proof.
        induction ls as [|?? IHls]; intro H; inversion H; subst; simpl;
        solve [ left; apply H0; assumption
              | right; apply IHls; assumption ].
      Qed.

      Lemma InA_map3 `{Reflexive _ eqPA} x1 ls
      : InA eqPB x1 (List.map f ls) -> exists x0, InA eqPA x0 ls /\ eqPB x1 (f x0).
      Proof.
        induction ls as [|?? IHls]; intro H'; inversion H'; clear H';
        repeat match goal with
                 | _ => progress subst
                 | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
                 | _ => progress simpl in *
                 | _ => progress destruct_head ex
                 | _ => progress destruct_head and
               end;
        solve [ eexists; split; [ | eassumption ];
                first [ left; reflexivity
                      | right; eassumption ] ].
      Qed.

      Lemma InA_map3' `{Reflexive _ eqPA} x1 ls
      : InA eqPB x1 (List.map f ls) -> exists x0, InA eqPA x0 ls.
      Proof.
        intro H'; apply InA_map3 in H'.
        destruct_head ex;
          destruct_head and;
          eexists; eassumption.
      Qed.
    End InA_map.

    Local Ltac NoDupA_map_t :=
      repeat match goal with
               | _ => intro
               | _ => progress simpl in *
               | _ => progress subst
               | _ => assumption
               | [ |- _ <-> _ ] => split
               | [ H : NoDupA _ (_::_) |- _ ] => (inversion H; clear H)
               | [ |- NoDupA _ nil ] => constructor
               | [ |- NoDupA _ (_::_) ] => constructor
               | _ => progress destruct_head prod
               | _ => progress destruct_head option
               | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
               | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
               | [ H : InA _ _ (filter_some _) |- _ ] => unique pose proof (@InA_filter_some_fst _ _ _ _ _ _ H)
               | _ => progress unfold not in *
               | _ => solve [ eauto using InA_map1, InA_map2 ]
             end.

    Lemma NoDupA_map1 {A B} (eqA : relation A) (eqB : relation B) (f : A -> B)
          ls
          (H : forall a a', eqA a a' -> eqB (f a) (f a'))
    : NoDupA eqB (List.map f ls) -> NoDupA eqA ls.
    Proof.
      induction ls; NoDupA_map_t.
    Qed.

    Lemma NoDupA_map2 {A B} (eqA : relation A) (eqB : relation B) (f : A -> B)
          ls
          (H : forall a a', eqB (f a) (f a') -> eqA a a')
    : NoDupA eqA ls -> NoDupA eqB (List.map f ls).
    Proof.
      induction ls; NoDupA_map_t.
    Qed.

    Definition elements (m : t elt) : list (key * elt)
      := filter_some (List.map (fun kv => (fst kv, snd (snd kv))) (M.elements m)).

    Definition cardinal (m : t elt) : nat
      := List.length (elements m).

    Definition fold {A} (f : key -> elt -> A -> A) (m : t elt) (init : A) : A
      := List.fold_left (fun acc kv => f (fst kv) (snd kv) acc) (elements m) init.

    Definition equal (eq : elt -> elt -> bool) (m1 : t elt) (m2 : t elt) : bool
      := M.equal (fun v1 v2 => match v1, v2 with
                                 | None, None => true
                                 | Some v1', Some v2' => eq v1' v2'
                                 | _, _ => false
                               end)
                 (M.map (@snd _ _) m1)
                 (M.map (@snd _ _) m2).


    Section Spec.
      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

      Definition MapsTo (k : key) (v : elt) (m : t elt)
        := exists gen, M.MapsTo k (gen, Some v) m.

      Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

      Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

      Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').

      Definition eq_key_elt (p p':key*elt) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

    Local Ltac pre_t :=
      repeat match goal with
               | _ => progress unfold remove, In, MapsTo, find, elements in *
               | [ |- appcontext[match ?E with _ => _ end] ] => case_eq E
               | _ => progress simpl in *
               | _ => intro
               | _ => progress destruct_head ex
               | _ => progress destruct_head and
               | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
               | _ => progress destruct_head prod
               | _ => progress subst
             end.

      Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
      Proof.
        unfold MapsTo; intros; destruct_head ex.
        eexists; eapply M.MapsTo_1; eassumption.
      Qed.

      Lemma mem_1 : In x m -> mem x m = true.
      Proof.
        unfold mem, In, MapsTo; intros.
        destruct_head ex.
        erewrite M.find_1 by eassumption; reflexivity.
      Qed.
      Lemma mem_2 : mem x m = true -> In x m.
      Proof.
        unfold mem, In, MapsTo.
        case_eq (M.find x m); intros p H;
        repeat match goal with
                 | [ |- appcontext[match ?E with _ => _ end] ] => case_eq E; intro
                 | _ => intro
                 | _ => progress subst
                 | [ H : M.find _ _ = Some _ |- _ ] => apply M.find_2 in H
                 | [ H : true = false |- _ ] => solve [ inversion H ]
                 | [ H : false = true |- _ ] => solve [ inversion H ]
                 | _ => repeat esplit; eassumption
               end.
      Qed.

      Lemma empty_1 : Empty empty.
      Proof.
        unfold empty, Empty, MapsTo.
        intros a e0 [gen H].
        apply M.empty_1 in H.
        assumption.
      Qed.

      Lemma fold_left_andb_true_InA {A} eqP `{Reflexive _ eqP}
            (f : A -> bool)
            `{Proper _ (eqP ==> Logic.eq) f}
            (ls : list A)
      : fold_left (fun b x => b && f x) ls true = true
        <-> (forall x, InA eqP x ls -> f x = true).
      Proof.
        rewrite fold_left_andb_true; split.
        { intros H' x0 H''.
          apply InA_alt in H''.
          destruct H'' as [y0 [H'' H''']].
          rewrite H''; auto. }
        { intros H' x0 X''.
          apply H'; apply InA_alt.
          eexists; split; [ reflexivity | assumption ]. }
      Qed.

      Local Instance : Reflexive (M.eq_key_elt (elt:=nat * option elt)).
      Proof.
        intro; destruct_head prod; split; try reflexivity; simpl.
        apply E.eq_refl.
      Qed.

      Local Instance
      : Proper (M.eq_key_elt (elt:=nat * option elt) ==> eq)
               (fun x0 : M.key * (nat * option elt) =>
                  match snd (snd x0) with
                    | Some _ => false
                    | None => true
                  end).
      Proof.
        hnf; simpl; clear.
        intros [??] [??] **; hnf in *;
          destruct_head and;
          subst.
        reflexivity.
      Qed.

      Lemma is_empty_1 : Empty m -> is_empty m = true.
      Proof.
        unfold Empty, is_empty, MapsTo.
        rewrite M.fold_1.
        intro H.
        apply (@fold_left_andb_true_InA _ (@M.eq_key_elt _) _ _ _).
        intros [k [gen [v|]]] H'; try reflexivity.
        exfalso.
        specialize (fun H' => H k v (ex_intro _ gen H')); simpl in *.
        apply M.elements_2 in H'; auto.
      Qed.

      Lemma is_empty_2 : is_empty m = true -> Empty m.
      Proof.
        unfold is_empty, Empty, MapsTo.
        rewrite M.fold_1.
        intro H.
        pose proof (proj1 (fold_left_andb_true_InA _) H) as H'; clear H; simpl in *.
        intros k v [gen H].
        specialize (H' (k, (gen, (Some v)))); simpl in *.
        cut (false = true); [ let H := fresh in intro H; inversion H | ].
        apply H'.
        apply M.elements_1 in H; auto.
      Qed.

      Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
      Proof.
        unfold MapsTo, add.
        intro H'.
        case_eq (M.find x m).
        { intros [gen ?] H''.
          apply M.find_2 in H''.
          exists (S gen).
          apply M.add_1; trivial. }
        { intro H''.
          exists 0.
          apply M.add_1; trivial. }
      Qed.
      Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Proof.
        unfold MapsTo, add.
        intros H [gen H'].
        exists gen.
        apply M.add_2; trivial.
      Qed.
      Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
      Proof.
        unfold MapsTo, add.
        intros H [gen H'].
        exists gen.
        apply M.add_3 in H'; trivial.
      Qed.

      Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
      Proof.
        clear.
        pre_t;
        add_facts.
      Qed.

      Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      Proof.
        clear.
        pre_t.
        { eexists; eapply M.add_2; eassumption. }
        { eexists; eassumption. }
      Qed.

      Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
      Proof.
        clear.
        pre_t; try solve [ eexists; eassumption ].
        eexists; eapply M.add_3; try eassumption.
        intro.
        add_facts.
      Qed.

      Lemma find_1 : MapsTo x e m -> find x m = Some e.
      Proof.
        clear.
        pre_t;
        add_facts.
        reflexivity.
      Qed.

      Lemma find_2 : find x m = Some e -> MapsTo x e m.
      Proof.
        clear.
        pre_t;
        add_facts.
        eexists; eassumption.
      Qed.

      Lemma InA_filter_some_eq_key_elt {B : Type} ls a b
      : InA (fun p p' : E.t * B => E.eq (fst p) (fst p') /\ snd p = snd p')
            (a, b) (filter_some ls) <->
        InA
          (fun p p' : E.t * option B => E.eq (fst p) (fst p') /\ snd p = snd p')
          (a, Some b) ls.
      Proof.
        clear.
        apply (@InA_filter_some _ B (fun B p p' => E.eq (fst p) (fst p') /\ snd p = snd p')); simpl in *.
        { simpl; intros; split; intros; split; destruct_head and; congruence. }
        { intros ? ? ? [? H']; simpl in *; inversion H'. }
      Qed.

      Lemma elements_1 : MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
      Proof.
        clear.
        unfold MapsTo, elements.
        intros [gen H].
        apply M.elements_1 in H.
        apply InA_filter_some_eq_key_elt.
        eapply InA_map1; try eassumption.
        intros; hnf in *; pre_t; split; trivial.
      Qed.

      Lemma elements_2 : InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
      Proof.
        clear.
        unfold MapsTo, elements.
        intro H.
        apply InA_filter_some_eq_key_elt in H.
        eapply InA_map3 in H.
        { destruct H as [[k [gen v]] H]; simpl in *.
          exists gen; destruct_head and; subst.
          apply M.elements_2 in H.
          add_facts; assumption. }
        { typeclasses eauto. }
      Qed.

      Lemma elements_3w : NoDupA eq_key (elements m).
      Proof.
        clear.
        unfold elements.
        unfold eq_key.
        apply NoDupA_filter_some.
        eapply NoDupA_map2; try apply M.elements_3w; trivial.
      Qed.

      Lemma cardinal_1 : cardinal m = length (elements m).
      Proof.
        clear.
        reflexivity.
      Qed.

      Lemma fold_1 :
        forall (A : Type) (i : A) (f : key -> elt -> A -> A),
          fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
      Proof.
        clear.
        reflexivity.
      Qed.

      Definition Equal m m' := forall y, find y m = find y m'.
      Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
        (forall k, In k m <-> In k m') /\
        (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
      Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

      Variable cmp : elt -> elt -> bool.

      Lemma equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
      Proof.
        clear.
        unfold equal, Equivb, Equiv, In, MapsTo, Cmp; simpl.
        intros.
        apply M.equal_1.
        unfold M.Equivb, M.Equiv, Cmp;
        repeat match goal with
                 | _ => intro
                 | [ H : (ex _) -> ?T |- _ ]
                   => specialize (fun x p => H (ex_intro _ x p))
                 | [ H : forall a, ex _ -> _ |- _ ]
                   => specialize (fun a b p => H a (ex_intro _ b p))
                 | [ H : forall a b, ex _ -> _ |- _ ]
                   => specialize (fun a b c p => H a b (ex_intro _ c p))
                 | [ H : forall a b c, ex _ -> _ |- _ ]
                   => specialize (fun a b c d p => H a b c (ex_intro _ d p))
                 | _ => progress simpl in *
                 | _ => progress split_iff
                 | [ |- _ <-> _ ] => split
                 | [ |- _ /\ _ ] => split
                 | [ H : M.In _ (M.map _ _) |- _ ] => unique pose proof (M.map_2 H)
               end;
        admit.
      Qed.

      Lemma equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
      Proof.
        clear.
        unfold equal.
        intro H; apply M.equal_2 in H.
        unfold Equivb, M.Equivb, Equiv, M.Equiv in *.
        admit.
      Qed.
    End Spec.
  End elt.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
                  MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof.
    unfold MapsTo, map.
    intros; destruct_head ex.
    eexists.
    apply (fun g => @M.map_1 _ (nat * option elt') m x (g, Some e) (fun v => (fst v, option_map f (snd v))));
      eassumption.
  Qed.

  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
                  In x (map f m) -> In x m.
  Proof.
    unfold map, In, MapsTo.
    intros; destruct_head ex.
    pose proof (@M.map_2) as H'.
    specialize (fun a b c d e f g => H' a b c d e (ex_intro _ f g)); simpl in *.
    specialize (H' _ _ _ _ _ _ H).
    destruct_head_hnf ex.
    destruct_head_hnf prod.
    destruct_head_hnf option.
    { repeat eexists; eassumption. }
    { exfalso.
      match goal with
        | [ H : M.MapsTo ?x (_, None) ?m, H' : M.MapsTo ?x (?g, Some ?v) (M.map ?f ?m) |- _ ]
          => apply (M.map_1 f) in H
      end.
      add_facts.
      simpl in *.
      congruence. }
  Qed.


  Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
                            (f:key->elt->elt'), MapsTo x e m ->
                                                exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof.
    unfold key, t, mapi, In, MapsTo.
    intros ? ? ? ? ? ? [gen H].
    let f := match goal with |- appcontext[M.mapi ?f] => constr:f end in
    pose proof (M.mapi_1 f H) as H'; simpl in *.
    destruct_head_hnf ex.
    destruct_head_hnf prod.
    destruct_head_hnf and.
    destruct_head_hnf option.
    repeat esplit; eassumption.
  Qed.

  Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
                        (f:key->elt->elt'), In x (mapi f m) -> In x m.
  Proof.
    unfold key, t, mapi, In, MapsTo.
    intros ? ? ? ? ? [v [gen H]].
    pose proof (fun a b c d e f g => @M.mapi_2 a b c d e (ex_intro _ f g)) as H'; simpl in H'.
    specialize (H' _ _ _ _ _ _ H).
    destruct_head_hnf ex.
    destruct_head_hnf prod.
    destruct_head_hnf and.
    destruct_head_hnf option.
    { repeat esplit; eassumption. }
    { exfalso.
      match goal with
        | [ H : M.MapsTo ?x (_, None) ?m, H' : M.MapsTo ?x (?g, Some ?v) (M.mapi ?f ?m) |- _ ]
          => apply (M.mapi_1 f) in H
      end.
      destruct_head ex.
      destruct_head and.
      add_facts. }
  Qed.

  Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
                        (x:key)(f:option elt->option elt'->option elt''),
                   In x m \/ In x m' ->
                   find x (map2 f m m') = f (find x m) (find x m').
  Proof.
    unfold key, t, map2, In, MapsTo, find.
    intros; rewrite M.map2_1.
    { do 2 edestruct @M.find;
      destruct_head prod;
      destruct_head option;
      unfold option_map;
      simpl;
      match goal with
        | [ |- appcontext[match ?E with _ => _ end] ] => destruct E; reflexivity
      end. }
    { destruct_head or; [ left | right ];
      unfold M.In;
      destruct_head ex;
      repeat esplit; eassumption. }
  Qed.

  Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
                        (x:key)(f:option elt->option elt'->option elt''),
                   In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
    unfold key, t, map2, In, MapsTo, find.
    intros ? ? ? ? ? ? ? [v [gen H]].
    pose proof (fun a b c d e f g h i => @M.map2_2 a b c d e f g (ex_intro _ h i)) as H'; simpl in H'.
    specialize (H' _ _ _ _ _ _ _ _ H).
    destruct_head or; [ left | right ];
    destruct_head_hnf ex;
    destruct_head prod;
    destruct_head option;
    try solve [ repeat esplit; eassumption ];
    exfalso;
    [ pose proof (fun a b c d e f g h i => @M.map2_1 a b c d e f g (or_introl (ex_intro _ h i))) as H''
    | pose proof (fun a b c d e f g h i => @M.map2_1 a b c d e f g (or_intror (ex_intro _ h i))) as H'' ];
    match goal with
      | [ H : M.MapsTo ?x (_, None) _, H' : M.MapsTo ?x (?g, Some ?v) (M.map2 ?f ?m ?m') |- _ ]
        => specialize (H'' _ _ _ m m' _ f _ H);
          let f' := fresh in
          let H''' := fresh in
          set (f' := f) in *;
            assert (H''' : id (f = f')) by reflexivity;
            clearbody f';
            revert H H' H'' H'''; clear; intros
    end;
    destruct_head ex;
    destruct_head and;
    add_facts;
    try solve [ unfold id, option_map in *; subst;
    repeat match goal with
             | [ H : appcontext[match ?f ?x ?m with _ => _ end] |- _ ]
               => destruct (f x m)
             (*| [ H : M.find ?x ?m = _, H' : appcontext[match M.find ?x ?m with _ => _ end] |- _ ]
               => rewrite H in H'
             | [ H : appcontext[match M.find ?x ?m with _ => _ end] |- _ ]
               => let H' := fresh in
                  case_eq (M.find x m);
                    [ intros ? H'; rewrite H' in H
                    | intro H'; rewrite H' in H ]*)
             | _ => progress destruct_head prod
             | _ => progress destruct_head option
             | _ => congruence
           end ].
    congruence.


    case_eq (M.find x m').
 }
    intros; rewrite M.map2_1.
    { do 2 edestruct @M.find;
      destruct_head prod;
      destruct_head option;
      match goal with
        | [ |- appcontext[match ?E with _ => _ end] ] => destruct E; reflexivity
      end. }
    { destruct_head or; [ left | right ];
      unfold M.In;
      destruct_head ex;
      repeat esplit; eassumption. }
    admit.
  Qed.

  Definition lt_key := M.lt_key.

  Lemma Forall_filter_some {A B} (P : A -> Prop) ls
  : List.Forall (fun p => P (fst p)) ls
    -> List.Forall (fun p => P (fst p)) (filter_some (B := B) ls).
  Proof.
    induction ls; intro H; destruct_head prod; destruct_head option; inversion H; subst;
    try constructor; eauto.
  Qed.

  Lemma Sorted_filter_some {A} f `{Transitive A f} {B} ls
  : Sorted (fun p p' : A * option B => f (fst p) (fst p')) ls
    -> Sorted (fun p p' => f (fst p) (fst p')) (filter_some ls).
  Proof.
    intro H'.
    apply Sorted_StronglySorted in H'; try solve [ repeat intro; etransitivity; eassumption ].
    apply StronglySorted_Sorted; try solve [ repeat intro; etransitivity; eassumption ].
    induction H'; try solve [ constructor ].
    destruct_head prod; destruct_head option; simpl; trivial;
    constructor; trivial.
    apply Forall_filter_some; trivial.
  Qed.

  Lemma Sorted_map {A B} (lt : relation A) (lt' : relation B) (f : A -> B)
        (H : forall x y, lt x y -> lt' (f x) (f y)) ls
  : Sorted lt ls -> Sorted lt' (List.map f ls).
  Proof.
    induction ls; intro H'; simpl; constructor;
    inversion H'; subst; eauto.
    destruct_head HdRel; constructor; eauto.
  Qed.

  Lemma elements_3 : forall (elt : Type) (m : t elt),
                       Sorted (lt_key (elt:=elt)) (elements m).
  Proof.
    unfold elements; intros.
    unfold lt_key.
    unfold M.lt_key.
    apply Sorted_filter_some; try solve [ hnf; apply E.lt_trans ].
    eapply Sorted_map; try apply M.elements_3.
    unfold M.lt_key; simpl; trivial.
  Qed.




  Definition elements_to_string {elt} (elt_to_string : elt -> string) (ls : list (key * (nat * option elt)))
  : string.
  Proof.
    Require Import String.
    SearchAbout nat string.
    pose (M.elements m).

      := filter_some (List.map (fun kv => (fst kv, snd (snd kv))) (M.elements m)).


  Definition to_string {elt} (elt_to_string : elt -> string) (m : t elt) : string.
  Proof.

  Defined.

End MakeSerializableMergableMap.

Static signature for Weak Maps
Similar to WSfun but expressed in a self-contained way.

Module Type WS.
  Declare Module E : DecidableType.
  Include WSfun E.
End WS.

Maps on ordered keys, functorial signature

Module Type Sfun (E : OrderedType).
  Include WSfun E.
  Section elt.
  Variable elt:Type.
   Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').
   Parameter elements_3 : forall m, sort lt_key (elements m).
Remark: since fold is specified via elements, this stronger specification of elements has an indirect impact on fold, which can now be proved to receive elements in increasing order.
  End elt.
End MakeSerializableMergableMap.
  Include Sfun E.


  Section elt.
    Variable elt : Type.

    Parameter to_string : forall (elt_to_string : elt -> string),
                            t elt -> string.

    Parameter from_string : forall (elt_from_string : string -> option elt),
                              string -> option (t elt).

    Section laws.
      Variable elt_to_string : elt -> string.
      Variable elt_from_string : string -> option elt.

      Axiom to_from_string
      : (forall s, match elt_from_string s with
                     | None => True
                     | Some x => elt_to_string x = s
                   end)
        -> forall s, match from_string elt_from_string s with
                       | None => True
                       | Some x => to_string elt_to_string x = s
                     end.
      Axiom from_to_string
      : (forall x, elt_from_string (elt_to_string x) = Some x)
        -> forall x, from_string elt_from_string (to_string elt_to_string x) = Some x.
    End laws.

    Parameter update : key -> elt -> t elt -> t elt.
    (** [update x y m] returns a map containing the same bindings as
        [m], plus a binding of [x] to [y]. If [x] was already bound in
        [m], its previous binding is merged with its new binding. *)
  End elt.
End SerializableMergableMapInterface.
