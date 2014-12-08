Require Import Coq.Strings.String Coq.FSets.FMapInterface Coq.Classes.RelationPairs.
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
             | [ H : appcontext[M.map2 ?f _ _] |- _ ]
               => not atomic f;
                 let f' := fresh "f" in
                 set (f' := f) in *
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
             | [ H : M.MapsTo ?k ?v ?m |- _ ]
               => unique pose proof (ex_intro (fun v => M.MapsTo k v m) v H : M.In k m)
             | [ H : M.In ?x (M.map2 ?f ?m ?m') |- _ ]
               => unique pose proof (M.map2_2 H)
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
                     | Some (gen1, None), Some (gen2, None)
                       => Some (max gen1 gen2, None)
                     | Some (gen1, v1'), Some (gen2, v2')
                       => Some (max gen1 gen2, f v1' v2')
                     | Some (gen1, None), None
                       => Some (gen1, None)
                     | Some (gen1, v1'), None
                       => Some (gen1, f v1' None)
                     | None, Some (gen2, None)
                       => Some (gen2, None)
                     | None, Some (gen2, v2')
                       => Some (gen2, f None v2')
                     | None, None => None
                   end)
                m m'.

    Definition garbage_collect (m : t elt) : t elt
      := M.map2 (fun v1 _ =>
                   match v1 with
                     | Some (_, None) => None
                     | Some (_, Some v) => Some (0, Some v)
                     | None => None
                   end)
                m m.

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
                 | _ => progress cleanup
                 | _ => progress simpl in *
                 | _ => progress destruct_head ex
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
               | _ => progress cleanup
               | [ |- _ <-> _ ] => split
               | [ H : NoDupA _ (_::_) |- _ ] => (inversion H; clear H)
               | [ |- NoDupA _ nil ] => constructor
               | [ |- NoDupA _ (_::_) ] => constructor
               | _ => progress destruct_head option
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
      := M.equal (fun v1 v2 => match snd v1, snd v2 with
                                 | None, None => true
                                 | Some v1', Some v2' => eq v1' v2'
                                 | _, _ => false
                               end)
                 (garbage_collect m1)
                 (garbage_collect m2).


    Lemma garbage_collect_1 m k gen
    : ~M.MapsTo k (gen, None) (garbage_collect m).
    Proof.
      clear.
      unfold garbage_collect; intro H.
      add_facts; cleanup.
      subst_body.
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | [ H : _ |- _ ] => rewrite M.map2_1 in H by assumption
             end.
    Qed.

    Lemma garbage_collect_2 m k v gen
    : M.MapsTo k (gen, Some v) (garbage_collect m)
      -> gen = 0 /\ exists gen', M.MapsTo k (gen', Some v) m.
    Proof.
      clear.
      unfold garbage_collect; intro H.
      add_facts; cleanup;
      subst_body;
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | [ H : _ |- _ ] => rewrite M.map2_1 in H by assumption
               | [ H : M.find ?x ?m = Some ?e |- _ ]
                 => unique pose proof (M.find_2 H)
               | _ => solve [ eauto ]
             end.
    Qed.

    Lemma garbage_collect_3 m k v gen
    : M.MapsTo k (gen, Some v) m
      -> M.MapsTo k (0, Some v) (garbage_collect m).
    Proof.
      clear.
      unfold garbage_collect; intro H.
      apply M.find_2.
      add_facts; cleanup.
      rewrite M.map2_1 by eauto;
        cleanup.
    Qed.

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
                 | _ => progress cleanup
                 | [ H : M.find _ _ = Some _ |- _ ] => apply M.find_2 in H
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
        intro; destruct_head prod; split; reflexivity.
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
                 | [ H : forall a b c d, ex _ -> _ |- _ ]
                   => specialize (fun a b c d e p => H a b c d (ex_intro _ e p))
                 | [ H : forall a b c d e, ex _ -> _ |- _ ]
                   => specialize (fun a b c d e f p => H a b c d e (ex_intro _ f p))
                 | _ => progress simpl in *
                 | _ => progress destruct_head_hnf ex
                 | _ => progress split_iff
                 | [ |- _ <-> _ ] => split
                 | [ |- _ /\ _ ] => split
                 | [ H : M.In _ (M.map _ _) |- _ ] => unique pose proof (M.map_2 H)
               end;
        repeat match goal with
                 | _ => progress cleanup
                 | _ => progress destruct_head option
                 | _ => progress destruct_head ex
                 | [ H : M.MapsTo _ (_, None) (garbage_collect _) |- _ ]
                   => apply garbage_collect_1 in H
                 | [ H : M.MapsTo _ (_, Some _) (garbage_collect _) |- _ ]
                   => apply garbage_collect_2 in H
               end;
        repeat match goal with
                 | [ H : forall a b c, M.MapsTo _ _ _ -> _, H' : M.MapsTo _ _ _ |- _ ]
                   => unique pose proof (H _ _ _ H')
               end;
        repeat match goal with
                 | _ => progress cleanup
                 | _ => progress destruct_head option
                 | _ => progress destruct_head ex
                 | [ H : M.MapsTo _ (_, None) (garbage_collect _) |- _ ]
                   => apply garbage_collect_1 in H
                 | [ H : M.MapsTo _ (_, Some _) (garbage_collect _) |- _ ]
                   => apply garbage_collect_2 in H
                 | _ => solve [ esplit; eauto using garbage_collect_3
                              | eauto ]
               end.
      Qed.

      Lemma equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
      Proof.
        clear.
        unfold equal.
        intro H; apply M.equal_2 in H.
        unfold Equivb, M.Equivb, Equiv, M.Equiv, Cmp, In, M.In, MapsTo in *.
        repeat match goal with
                 | _ => intro
                 | _ => progress cleanup
                 | _ => progress simpl in *
                 | _ => progress destruct_head ex
                 | [ |- _ <-> _ ] => split
                 | _=> progress split_iff
                 | [ H : (ex _) -> ?T |- _ ]
                   => specialize (fun x p => H (ex_intro _ x p))
                 | [ H : forall a, ex _ -> _ |- _ ]
                   => specialize (fun a b p => H a (ex_intro _ b p))
                 | [ H : forall a b, ex _ -> _ |- _ ]
                   => specialize (fun a b c p => H a b (ex_intro _ c p))
                 | [ H : forall a b c, ex _ -> _ |- _ ]
                   => specialize (fun a b c d p => H a b c (ex_intro _ d p))
                 | [ H : forall a b c d, ex _ -> _ |- _ ]
                   => specialize (fun a b c d e p => H a b c d (ex_intro _ e p))
                 | [ H : forall a b c d e, ex _ -> _ |- _ ]
                   => specialize (fun a b c d e f p => H a b c d e (ex_intro _ f p))
               end;
        repeat match goal with
                 | [ H : M.MapsTo _ (_, Some _) ?m |- _ ]
                   => atomic m; unique pose proof (garbage_collect_3 H)
                 | [ H : forall a b, M.MapsTo _ _ _ -> _, H' : M.MapsTo _ _ _ |- _ ]
                   => unique pose proof (H _ _ H')
               end;
        destruct_head ex;
        cleanup;
        destruct_head option;
        repeat match goal with
                 | [ H : M.MapsTo _ (_, Some _) (garbage_collect _) |- _ ]
                   => unique pose proof (garbage_collect_2 H)
               end;
        repeat match goal with
                 | _ => intro
                 | _ => progress cleanup
                 | _ => progress simpl in *
                 | _ => progress destruct_head option
                 | _ => progress destruct_head ex
                 | [ H : M.MapsTo _ (_, None) (garbage_collect _) |- _ ]
                   => apply garbage_collect_1 in H
                 | _ => solve [ eauto ]
               end.
        repeat match goal with
                 | [ H : forall a, M.MapsTo _ _ _ -> _, H' : M.MapsTo _ _ _ |- _ ]
                   => unique pose proof (H _ H')
                 | [ H : forall a b c, M.MapsTo _ _ _ -> _, H' : M.MapsTo _ _ _ |- _ ]
                   => unique pose proof (fun c => H _ _ c H')
               end.
        simpl in *.
        eauto.
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
    { destruct_head or;
      destruct_head ex;
      add_facts; cleanup;
      do 2 edestruct @M.find;
      cleanup;
      destruct_head option;
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
    match goal with
      | [ H : M.In ?x ?m \/ M.In ?x ?m' |- _ ] =>
        case_eq (M.find x m);
          case_eq (M.find x m');
          intros
    end;
      destruct_head or;
      destruct_head_hnf ex;
      destruct_head prod;
      destruct_head option;
      try solve [ left; repeat esplit; eassumption
                | right; repeat esplit; eassumption ];
      (lazymatch goal with
      | [ H : M.MapsTo ?x (_, None) ?m, H' : M.find ?x ?m = Some (_, Some _) |- _ ]
        => (exfalso; revert H H'; clear;
            intros;
            add_facts;
            congruence)
      | [ H : M.MapsTo ?x (_, _) ?m, H' : M.find ?x ?m = None |- _ ]
        => (exfalso; revert H H'; clear;
            intros;
            add_facts;
            congruence)
      | _ => idtac
       end);
      try solve [ left; repeat esplit; apply M.find_2; eassumption
                | right; repeat esplit; apply M.find_2; eassumption ];
      try match goal with
            | [ H : M.MapsTo _ _ (M.map2 _ _ _) |- _ ]
              => apply M.find_1 in H;
                rewrite M.map2_1 in H by constructor (repeat esplit; apply M.find_2; eassumption)
          end;
      cleanup.
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

  Section merge.
    Variable elt : Type.

    Definition merge (m1 : t elt) (m2 : t elt) : t elt
      := M.map2
           (fun a b
            => match a, b with
                 | Some (gen0, v0), Some (gen1, v1)
                   => Some (if (Compare_dec.leb gen0 gen1 : bool)%nat
                            then (gen1, v1)
                            else (gen0, v0))
                 | Some gv, None => Some gv
                 | None, Some gv => Some gv
                 | None, None => None
               end)
           m1 m2.

    Lemma merge_In_1 : forall k m1 m2, In k m1 -> In k m2 -> In k (merge m1 m2).
    Proof.
      unfold In, merge, MapsTo.
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress destruct_head ex
               | [ H : M.MapsTo _ _ _ |- _ ] => unique pose proof (M.find_1 H)
               | _ => setoid_rewrite <- (@M.find_2 : forall a b c d, impl _ _)
               | _ => rewrite M.map2_1
               | [ |- appcontext[match ?E with _ => _ end] ] => case_eq E
               | _ => solve [ repeat esplit
                            | left; repeat esplit; eassumption
                            | right; repeat esplit; eassumption ]
             end.
    Qed.

    Lemma merge_In_2 : forall k m1 m2, In k (merge m1 m2) -> In k m1 \/ In k m2.
    Proof.
      unfold In, merge, MapsTo.
      intros; destruct_head ex.
      (lazymatch goal with
        | [ H : M.MapsTo ?k ?v (M.map2 ?f ?m1 ?m2) |- _ ]
          => (idtac;
              let T := constr:(fun a b c d e f' g h i => @M.map2_2 a b c d e f' g (ex_intro _ h i)) in
              let H' := fresh in
              pose proof (M.map2_1 f (T _ _ _ _ _ _ _ _ H)) as H';
              apply M.find_1 in H;
              simpl in *;
                rewrite H' in H)
       end).
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress destruct_head_hnf ex
               | _ => progress destruct_head or
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | _ => setoid_rewrite <- (@M.find_2 : forall a b c d, impl _ _)
               | _ => solve [ repeat esplit
                            | left; repeat esplit; eassumption
                            | right; repeat esplit; eassumption ]
             end.
    Qed.

    Lemma merge_find_1 : forall k v m1 m2, find k m1 = Some v -> find k m2 = Some v -> find k (merge m1 m2) = Some v.
    Proof.
      unfold find, merge.
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress destruct_head_hnf ex
               | _ => progress destruct_head or
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | [ |- appcontext[match ?E with _ => _ end] ]
                 => case_eq E
               | _ => setoid_rewrite <- (@M.find_2 : forall a b c d, impl _ _)
               | _ => rewrite M.map2_1
               | _ => solve [ repeat esplit
                            | left; repeat esplit; eassumption
                            | right; repeat esplit; eassumption ]
             end;
      repeat match goal with
               | [ H : M.find ?x ?m = Some ?e |- _ ]
                 => unique pose proof (M.find_2 H)
               | [ H : M.MapsTo ?k ?v ?m |- _ ]
                 => unique pose proof (ex_intro (fun v => M.MapsTo k v m) v H : M.In k m)
               | [ H : context[M.map2 ?f ?m1 ?m2], H' : M.In ?k ?m1 |- _ ]
                 => unique pose proof (M.map2_1 (m := m1) (m' := m2) f (or_introl H'))
               | [ H : context[M.map2 ?f ?m1 ?m2], H' : M.In ?k ?m2 |- _ ]
                 => unique pose proof (M.map2_1 (m := m1) (m' := m2) f (or_intror H'))
             end;
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress simpl in *
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | [ |- appcontext[match ?E with _ => _ end] ]
                 => case_eq E
             end.
    Qed.

    Lemma merge_find_2 : forall k v m1 m2, find k m1 = None -> find k (merge m1 m2) = Some v -> find k m2 = Some v.
    Proof.
      unfold find, merge.
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress destruct_head_hnf ex
               | _ => progress destruct_head or
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | [ |- appcontext[match ?E with _ => _ end] ]
                 => case_eq E
               | _ => setoid_rewrite <- (@M.find_2 : forall a b c d, impl _ _)
               | _ => rewrite M.map2_1
               | _ => solve [ repeat esplit
                            | left; repeat esplit; eassumption
                            | right; repeat esplit; eassumption ]
             end;
      repeat match goal with
               | [ H : M.find ?x ?m = Some ?e |- _ ]
                 => unique pose proof (M.find_2 H)
               | [ H : M.MapsTo ?k ?v ?m |- _ ]
                 => unique pose proof (ex_intro (fun v => M.MapsTo k v m) v H : M.In k m)
               | [ H : context[M.map2 ?f ?m1 ?m2], H' : M.In ?k ?m1 |- _ ]
                 => unique pose proof (M.map2_1 (m := m1) (m' := m2) f (or_introl H'))
               | [ H' : M.In ?k (M.map2 ?f ?m1 ?m2) |- _ ]
                 => unique pose proof (M.map2_2 H')
               | [ H : context[M.map2 ?f ?m1 ?m2], H' : M.In ?k ?m2 |- _ ]
                 => unique pose proof (M.map2_1 (m := m1) (m' := m2) f (or_intror H'))
             end;
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress simpl in *
               | _ => progress destruct_head or
               | _ => progress destruct_head_hnf ex
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | [ |- appcontext[match ?E with _ => _ end] ]
                 => case_eq E
             end;
      repeat match goal with
               | [ H : appcontext[M.map2] |- _ ] => clear H
             end;
      add_facts; cleanup.
    Qed.

    Lemma merge_find_3 : forall k v m1 m2, find k m2 = None -> find k (merge m1 m2) = Some v -> find k m1 = Some v.
      unfold find, merge.
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress destruct_head_hnf ex
               | _ => progress destruct_head or
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | [ |- appcontext[match ?E with _ => _ end] ]
                 => case_eq E
               | _ => setoid_rewrite <- (@M.find_2 : forall a b c d, impl _ _)
               | _ => rewrite M.map2_1
               | _ => solve [ repeat esplit
                            | left; repeat esplit; eassumption
                            | right; repeat esplit; eassumption ]
             end;
      repeat match goal with
               | [ H : M.find ?x ?m = Some ?e |- _ ]
                 => unique pose proof (M.find_2 H)
               | [ H : M.MapsTo ?k ?v ?m |- _ ]
                 => unique pose proof (ex_intro (fun v => M.MapsTo k v m) v H : M.In k m)
               | [ H : context[M.map2 ?f ?m1 ?m2], H' : M.In ?k ?m1 |- _ ]
                 => unique pose proof (M.map2_1 (m := m1) (m' := m2) f (or_introl H'))
               | [ H' : M.In ?k (M.map2 ?f ?m1 ?m2) |- _ ]
                 => unique pose proof (M.map2_2 H')
               | [ H : context[M.map2 ?f ?m1 ?m2], H' : M.In ?k ?m2 |- _ ]
                 => unique pose proof (M.map2_1 (m := m1) (m' := m2) f (or_intror H'))
             end;
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress simpl in *
               | _ => progress destruct_head or
               | _ => progress destruct_head_hnf ex
               | [ H : appcontext[match ?E with _ => _ end] |- _ ]
                 => revert H; case_eq E
               | [ |- appcontext[match ?E with _ => _ end] ]
                 => case_eq E
             end;
      repeat match goal with
               | [ H : appcontext[M.map2] |- _ ] => clear H
             end;
      add_facts; cleanup.
    Qed.
  End merge.


  Definition from_internal_elements {elt} (elements : list (M.key * (nat * option elt)))
  : t elt
    := fold_right
         (fun kv acc => M.add (fst kv) (snd kv) acc)
         (@M.empty _)
         elements.

  Lemma not_eq_InA {A B} (k k' : A) (v v' : B) (RA : relation A) (R R' : relation (A * B))
        (ls : list (A * B))
        (H0 : InA R (k, v) ls)
        (H1 : ~InA R' (k', v') ls)
        (HR : forall a, R (k, v) a -> RA k' k -> R' (k', v') a)
  : ~RA k' k.
  Proof.
    induction ls; inversion H0; clear H0; subst.
    { intro H'; apply H1; left; eauto. }
    { apply IHls; eauto. }
  Qed.

  Local Ltac split_ex_in_hyps :=
    repeat match goal with
             | [ H : (ex _) -> ?T |- _ ]
               => specialize (fun x p => H (ex_intro _ x p))
             | [ H : forall a, ex _ -> _ |- _ ]
               => specialize (fun a b p => H a (ex_intro _ b p))
             | [ H : forall a b, ex _ -> _ |- _ ]
               => specialize (fun a b c p => H a b (ex_intro _ c p))
             | [ H : forall a b c, ex _ -> _ |- _ ]
               => specialize (fun a b c d p => H a b c (ex_intro _ d p))
             | [ H : forall a b c d, ex _ -> _ |- _ ]
               => specialize (fun a b c d e p => H a b c d (ex_intro _ e p))
             | [ H : forall a b c d e, ex _ -> _ |- _ ]
               => specialize (fun a b c d e f p => H a b c d e (ex_intro _ f p))
             | [ H : forall a, and _ _ -> _ |- _ ]
               => specialize (fun a c d => H a (conj c d))
             | [ H : forall a b, and _ _ -> _ |- _ ]
               => specialize (fun a b c d => H a b (conj c d))
             | [ H : forall a b c d, and _ _ -> _ |- _ ]
               => specialize (fun a b c d x y => H a b c d(conj x y))
             | [ H : forall a b c d e f, and _ _ -> _ |- _ ]
               => specialize (fun a b c d e f x y => H a b c d e f (conj x y))
             | [ H : forall (z : prod _  _), _ |- _ ]
               => specialize (fun x y => H (x, y))
             | [ H : forall a (z : prod _  _), _ |- _ ]
               => specialize (fun a x y => H a (x, y))
             | [ H : forall a b (z : prod _  _), _ |- _ ]
               => specialize (fun a b x y => H a b (x, y))
             | [ H : forall a b c (z : prod _  _), _ |- _ ]
               => specialize (fun a b c x y => H a b c (x, y))
             | [ H : forall a b c d (z : prod _  _), _ |- _ ]
               => specialize (fun a b c d x y => H a b c d (x, y))
             | _ => progress simpl in *
           end.

  Lemma InA_NoDupA_eq {A R R'} `{Symmetric A R, Transitive A R, Equivalence A R'}
        (x y : A)
        (ls : list A)
        (H_0 : InA R x ls)
        (H_1 : InA R y ls)
        (H_D : NoDupA R' ls)
        (HRR' : forall a b, R a b -> R' a b)
        (HR' : R' x y)
  : R x y.
  Proof.
    induction ls;
    inversion H_0; clear H_0; subst;
    inversion H_1; clear H_1; subst;
    inversion H_D; clear H_D; subst;
    eauto.
    { match goal with
        | [ H : ~_ |- _ ] => exfalso; apply H; clear H
      end.
      erewrite <- HRR' by eassumption.
      rewrite HR'; eauto.
      apply InA_alt.
      match goal with
        | [ H : InA _ _ _ |- _ ] => apply InA_alt in H
      end.
      destruct_head ex.
      destruct_head and.
      eauto. }
    { match goal with
        | [ H : ~_ |- _ ] => exfalso; apply H
      end.
      erewrite <- HRR' by eassumption.
      rewrite <- HR'; eauto.
      apply InA_alt.
      match goal with
        | [ H : InA _ _ _ |- _ ] => apply InA_alt in H
      end.
      destruct_head ex.
      destruct_head and.
      eauto. }
  Qed.

  Lemma InA_NoDupA_eq_fine_0 {A R0 R1 R'} `{Transitive A R', Symmetric A R'}
        (x y : A)
        (ls : list A)
        (H_0 : InA R0 x ls)
        (H_1 : InA R1 y ls)
        (H_D : NoDupA R' ls)
        (HR0R' : forall a b, R0 a b -> R' b a)
        (HR1R' : forall a b, R1 a b -> R' b a)
        (HR' : R' x y)
  : exists a, R0 x a /\ R1 y a.
  Proof.
    induction ls;
    inversion H_0; clear H_0; subst;
    inversion H_1; clear H_1; subst;
    inversion H_D; clear H_D; subst;
    eauto.
    { match goal with
        | [ H : ~_ |- _ ] => exfalso; apply H; clear H
      end.
      repeat match goal with
               | [ H : _ |- _ ] => setoid_rewrite InA_alt in H
               | _ => setoid_rewrite InA_alt
               | _ => progress destruct_head ex
               | _ => progress destruct_head and
               | _ => progress unfold Basics.flip in *
               | _ => solve [ repeat esplit; try eassumption; etransitivity; eauto ]
             end. }
    { match goal with
        | [ H : ~_ |- _ ] => exfalso; apply H; clear H
      end.
      repeat match goal with
               | [ H : _ |- _ ] => setoid_rewrite InA_alt in H
               | _ => setoid_rewrite InA_alt
               | _ => progress destruct_head ex
               | _ => progress destruct_head and
               | _ => progress unfold Basics.flip in *
               | _ => solve [ repeat esplit; try eassumption; etransitivity; eauto ]
             end. }
  Qed.

  Lemma InA_NoDupA_eq_fine_1 {A R R'} `{Transitive A R', Symmetric A R'}
        (x y : A)
        (ls : list A)
        (H_0 : InA R x ls)
        (H_1 : InA (Basics.flip R) y ls)
        (H_D : NoDupA R' ls)
        (HRR' : forall a b, R a b -> R' b a)
        (HR' : R' x y)
        (HRT : forall a, R x a -> R a y -> R x y)
  : R x y.
  Proof.
    induction ls;
    inversion H_0; clear H_0; subst;
    inversion H_1; clear H_1; subst;
    inversion H_D; clear H_D; subst;
    eauto.
    { match goal with
        | [ H : ~_ |- _ ] => exfalso; apply H; clear H
      end.
      repeat match goal with
               | [ H : _ |- _ ] => setoid_rewrite InA_alt in H
               | _ => setoid_rewrite InA_alt
               | _ => progress destruct_head ex
               | _ => progress destruct_head and
               | _ => progress unfold Basics.flip in *
               | _ => solve [ repeat esplit; try eassumption; eauto ]
             end. }
    { match goal with
        | [ H : ~_ |- _ ] => exfalso; apply H; clear H
      end.
      repeat match goal with
               | [ H : _ |- _ ] => setoid_rewrite InA_alt in H
               | _ => setoid_rewrite InA_alt
               | _ => progress destruct_head ex
               | _ => progress destruct_head and
               | _ => progress unfold Basics.flip in *
               | _ => solve [ repeat esplit; try eassumption; etransitivity; eauto ]
             end. }
  Qed.

  Lemma InA_from_internal_elements_1 {elt} (elements : list (M.key * (nat * option elt)))
        k v
        (H0 : NoDupA (@eq_key _) elements)
        (H1 : InA (@M.eq_key_elt _) (k, v) elements)
  : M.MapsTo k v (from_internal_elements elements).
  Proof.
    unfold from_internal_elements.
    induction elements;
    repeat match goal with
             | _ => progress destruct_head_hnf and
             | _ => progress cleanup
             | _ => progress simpl in *
             | [ H : InA _ _ nil |- _ ] => solve [ inversion H ]
             | [ H : InA _ _ (_::_) |- _ ] => (inversion H; clear H)
             | [ H : NoDupA _ nil |- _ ] => clear H
             | [ H : NoDupA _ (_::_) |- _ ] => (inversion H; clear H)
             | _ => apply M.add_1; solve [ assumption | apply E.eq_sym; assumption ]
           end.
    { apply M.add_2; eauto.
      eapply not_eq_InA; try eassumption; [].
      unfold M.eq_key_elt, eq_key; simpl; intros; cleanup.
      eapply E.eq_trans; eassumption. }
  Qed.

  Lemma InA_from_internal_elements_2 {elt} (elements : list (M.key * (nat * option elt)))
        k v
        (H : M.MapsTo k v (from_internal_elements elements))
  : InA (@M.eq_key_elt _) (k, v) elements.
  Proof.
    unfold from_internal_elements in *.
    induction elements;
    repeat match goal with
             | _ => progress destruct_head_hnf and
             | _ => progress cleanup
             | _ => progress simpl in *
             | [ H : InA _ _ nil |- _ ] => solve [ inversion H ]
             | [ H : InA _ _ (_::_) |- _ ] => (inversion H; clear H)
             | [ H : NoDupA _ nil |- _ ] => clear H
             | [ H : NoDupA _ (_::_) |- _ ] => (inversion H; clear H)
             | _ => apply M.add_1; solve [ assumption | apply E.eq_sym; assumption ]
             | [ H : M.MapsTo _ _ (M.empty _) |- _ ] => apply M.empty_1 in H
           end.
    match goal with
      | [ H : M.MapsTo ?k ?v (M.add ?k' ?v' ?m) |- _ ]
        => let H' := fresh in
           destruct (E.eq_dec k' k) as [H'|H'];
             [ left; unique pose proof (M.add_1 m v' H')
             | right; unique pose proof (M.add_3 H' H); eauto ]
    end.
    repeat match goal with
             | [ H : M.MapsTo ?x ?e ?m |- _ ]
               => unique pose proof (M.find_1 H)
           end;
      cleanup.
    split; simpl; eauto.
  Qed.

  Lemma from_internal_elements_Equal {elt} (m : t elt)
  : Equal m (from_internal_elements (M.elements m)).
  Proof.
    unfold Equal, find.
    intro k.
    repeat match goal with
             | _ => intro
             | _ => progress cleanup
             | [ |- appcontext[match ?E with _ => _ end] ] => case_eq E
           end;
    repeat match goal with
             | [ H : M.find ?x ?m = Some ?e |- _ ]
               => unique pose proof (M.find_2 H)
             | [ H : M.MapsTo ?k ?v ?m |- _ ]
               => unique pose proof (M.elements_1 H)
             | [ H : InA _ _ (M.elements ?m) |- _ ]
               => atomic m; unique pose proof (InA_from_internal_elements_1 (@M.elements_3w _ _) H)
             | [ H : M.MapsTo ?x ?e ?m |- _ ]
               => unique pose proof (M.find_1 H)
             | [ H : M.MapsTo ?x ?e (from_internal_elements ?ls) |- _ ]
               => unique pose proof (InA_from_internal_elements_2 _ H)
             | [ H : InA _ _ (M.elements ?m) |- _ ]
               => unique pose proof (M.elements_2 H)
           end;
      cleanup.
  Qed.

  Lemma from_internal_elements_equiv_refl {elt} R `{Reflexive elt R} (m : t elt)
  : Equiv R m (from_internal_elements (M.elements m)).
  Proof.
    generalize (from_internal_elements_Equal m).
    generalize (from_internal_elements (M.elements m)); intro.
    unfold Equal, Equiv, In.
    intro H'.
    split.
    { intro k; specialize (H' k).
      split; intros [e H''];
      apply find_1 in H'';
      eexists; apply find_2; cleanup; eauto. }
    { intros k e e' H'' H'''.
      specialize (H' k).
      apply find_1 in H''; apply find_1 in H'''.
      cleanup. }
  Qed.

  Fixpoint is_sorted {elt} (elements : list (M.key * (nat * option elt)))
  : bool
    := match elements with
         | nil => true
         | x::xs => match xs with
                      | nil => true
                      | y::ys => match E.compare (fst x) (fst y) with
                                   | LT _ => is_sorted xs
                                   | EQ _ => false
                                   | GT _ => false
                                 end
                    end
       end.

  Lemma Sorted_is_sorted {elt} ls
  : @is_sorted elt ls = true <-> Sorted (@M.lt_key _) ls.
  Proof.
    rewrite Sorted_LocallySorted_iff.
    induction ls; simpl; split; intros; try constructor; simpl in *;
    split_iff;
    generalize dependent (is_sorted ls); intros;
    destruct ls; simpl in *; try constructor;
    repeat match goal with
             | [ H : LocallySorted _ (_::_::_) |- _ ] => (inversion H; clear H)
             | _ => progress intuition subst
             | _ => progress hnf in *
             | [ H : E.lt ?a ?b |- _ ] => unique pose proof (E.lt_not_eq H : _ -> False)
             | [ H : E.lt ?a ?b, H' : E.lt ?b ?c |- _ ] => unique pose proof (E.lt_trans H H')
           end;
    edestruct E.compare;
    repeat match goal with
             | _ => progress subst
             | [ H : E.lt ?a ?b |- _ ] => unique pose proof (E.lt_not_eq H : _ -> False)
             | [ H : E.lt ?a ?b, H' : E.lt ?b ?c |- _ ] => unique pose proof (E.lt_trans H H')
             | [ H : False |- _ ] => destruct H
             | [ H : E.eq ?a ?a -> False |- _ ] => unique pose proof (H (E.eq_refl _))
             | _ => eauto; congruence
           end.
  Qed.

  Lemma not_Sorted_is_sorted {elt} ls
  : @is_sorted elt ls = false <-> ~Sorted (@M.lt_key _) ls.
  Proof.
    rewrite <- Sorted_is_sorted.
    destruct (is_sorted ls); split; congruence.
  Qed.

  Local Instance eq_prod_lt_compat {A R}
  : Proper
      (E.eq * R ==> E.eq * R ==> iff)
      (@M.lt_key A).
  Proof.
    lazy; intros; destruct_head prod; split; destruct_head and; intros;
    match goal with
      | [ H : E.eq ?b ?a, H' : E.lt ?b ?c, H'' : E.eq ?c ?d |- E.lt ?a ?d ]
        => destruct (E.compare a d); trivial; destruct (E.compare a c); destruct (E.compare b d)
      | [ H : E.eq ?a ?b, H' : E.lt ?b ?c, H'' : E.eq ?d ?c |- E.lt ?a ?d ]
        => destruct (E.compare a d); trivial; destruct (E.compare a c); destruct (E.compare b d)
    end;
    repeat match goal with
             | [ H : False |- _ ] => destruct H
             | [ H : E.eq ?x ?y |- _ ]
               => unique pose proof (E.eq_sym H)
             | [ x : key |- _ ]
               => unique pose proof (E.eq_refl x)
             | [ H : E.eq ?x ?y, H' : E.eq ?y ?z |- _ ]
               => unique pose proof (E.eq_trans H H')
             | [ H : E.lt ?x ?y, H' : E.lt ?y ?z |- _ ]
               => unique pose proof (E.lt_trans H H')
             | [ H : E.lt ?x ?y, H' : E.eq ?x ?y |- _ ]
               => unique pose proof (E.lt_not_eq H H')
           end.
  Qed.

  Local Instance eq_lt_compat {A}
  : Proper
      (@eq_key A ==> @eq_key A ==> iff)
      (@M.lt_key A).
  Proof.
    lazy; intros; destruct_head prod; split; intros;
    match goal with
      | [ H : E.eq ?b ?a, H' : E.lt ?b ?c, H'' : E.eq ?c ?d |- E.lt ?a ?d ]
        => destruct (E.compare a d); trivial; destruct (E.compare a c); destruct (E.compare b d)
      | [ H : E.eq ?a ?b, H' : E.lt ?b ?c, H'' : E.eq ?d ?c |- E.lt ?a ?d ]
        => destruct (E.compare a d); trivial; destruct (E.compare a c); destruct (E.compare b d)
    end;
    repeat match goal with
             | [ H : False |- _ ] => destruct H
             | [ H : E.eq ?x ?y |- _ ]
               => unique pose proof (E.eq_sym H)
             | [ x : key |- _ ]
               => unique pose proof (E.eq_refl x)
             | [ H : E.eq ?x ?y, H' : E.eq ?y ?z |- _ ]
               => unique pose proof (E.eq_trans H H')
             | [ H : E.lt ?x ?y, H' : E.lt ?y ?z |- _ ]
               => unique pose proof (E.lt_trans H H')
             | [ H : E.lt ?x ?y, H' : E.eq ?x ?y |- _ ]
               => unique pose proof (E.lt_not_eq H H')
           end.
  Qed.

  Lemma Sorted_eqlistA {elt} {R'} `{Transitive elt R'} {R : relation elt} ls ls'
        `{Proper _ (R ==> R ==> iff)%signature R'}
  : eqlistA R ls ls' -> (Sorted R' ls <-> Sorted R' ls').
  Proof.
    rewrite !Sorted_LocallySorted_iff.
    revert ls'; induction ls; intros ls' HE.
    { inversion HE; subst; reflexivity. }
    { split; intro Hls; inversion Hls; clear Hls; subst;
      inversion HE; clear HE; subst;
      repeat match goal with
               | _ => progress subst
               | _ => progress split_iff
               | [ H : eqlistA _ _ nil |- _ ] => (inversion H; clear H)
               | [ H : eqlistA _ nil _ |- _ ] => (inversion H; clear H)
               | [ H : eqlistA _ (_::_) ?x |- _ ] => (atomic x; inversion H)
               | [ H : eqlistA _ ?x (_::_) |- _ ] => (atomic x; inversion H)
               | _ => solve [ constructor | eauto ]
               | [ |- LocallySorted _ (_::_::_) ] => constructor; eauto
               | _ => progress unfold Proper, respectful, impl in *
             end. }
  Qed.

  Local Instance eq_key_Equivalence {A} : Equivalence (@eq_key A).
  Proof.
    split; typeclasses eauto.
  Qed.

  Local Instance lt_key_StrictOrder {A} : StrictOrder (@M.lt_key A).
  Proof.
    split.
    { intros x H'.
      apply E.lt_not_eq in H'.
      apply H', E.eq_refl. }
    { intros ???; apply E.lt_trans. }
  Qed.

  Lemma is_sorted_NoDupA {elt} ls
        (H : @is_sorted elt ls = true)
  : NoDupA (@eq_key _) ls.
  Proof.
    apply Sorted_is_sorted in H.
    eapply SortA_NoDupA; eauto; typeclasses eauto.
  Qed.

  Definition sorted_from_internal_elements {elt} (ls : option (list _))
    := match ls with
         | Some ls' => if @is_sorted elt ls'
                       then Some (from_internal_elements ls')
                       else None
         | None => None
       end.

  Local Instance Serializable_map {elt} `{Serializable elt} : Serializable (t elt)
    := {| to_string x := to_string (M.elements x) |}.

  Local Instance Deserializable_map {elt} `{Deserializable elt} : Deserializable (t elt)
    := {| from_string s := prod_map
                             (sorted_from_internal_elements)
                             id
                             (from_string (A := list (M.key * (nat * option elt))) s) |}.

  Local Opaque Serializable_list.
  Local Opaque Deserializable_list.

  Lemma eqlistA_nil {A R'} `{Reflexive A R'} {R} (ls : list A)
  : eqlistA R nil ls <-> forall x, ~InA R' x ls.
  Proof.
    destruct ls; split; auto.
    { intros H0 x H'; inversion H'. }
    { intro H0; inversion H0. }
    { intro H'; exfalso; eapply H'; left; reflexivity. }
  Qed.

  Local Instance MEquiv_Reflexive {elt eq_elt} `{Reflexive elt eq_elt}
  : Reflexive (@M.Equiv elt eq_elt).
  Proof.
    lazy; firstorder.
    add_facts; reflexivity.
  Qed.

  Local Instance Equiv_Transitive {elt eq_elt} `{Transitive elt eq_elt}
  : Transitive (@Equiv elt eq_elt).
  Proof.
    lazy.
    repeat match goal with
             | _ => intro
             | _ => progress cleanup
             | _ => progress destruct_head ex
             | _ => progress simpl in *
             | _ => solve [ eauto ]
             | [ H : (ex _) -> ?T |- _ ]
               => specialize (fun x p => H (ex_intro _ x p))
             | [ H : forall a, ex _ -> _ |- _ ]
               => specialize (fun a b p => H a (ex_intro _ b p))
             | [ H : forall a b, ex _ -> _ |- _ ]
               => specialize (fun a b c p => H a b (ex_intro _ c p))
             | [ H : forall a b c, ex _ -> _ |- _ ]
               => specialize (fun a b c d p => H a b c (ex_intro _ d p))
             | [ H : forall a b c d, ex _ -> _ |- _ ]
               => specialize (fun a b c d e p => H a b c d (ex_intro _ e p))
             | [ H : forall a b c d e, ex _ -> _ |- _ ]
               => specialize (fun a b c d e f p => H a b c d e (ex_intro _ f p))
           end.
    repeat match goal with
             | [ H : forall a b c d, M.MapsTo _ _ _ -> _, H' : M.MapsTo _ _ _ |- _]
               => unique pose proof (fun c => H _ _ c _ H')
             | [ H : forall a b c, M.MapsTo _ _ _ -> _, H' : M.MapsTo _ _ _ |- _]
               => unique pose proof (H _ _ _ H')
           end;
      destruct_head ex.
    eauto.
  Qed.

  Lemma InA_impl {A} (R1 R2 : relation A) x ls
        (H' : InA R1 x ls)
        (H : forall a, R1 x a -> R2 x a)
  : InA R2 x ls.
  Proof.
    induction ls; inversion H'; clear H'; subst.
    { left; eauto. }
    { right; eauto. }
  Qed.

  Lemma adj_elements_helper {elt} eq_elt `{Equivalence elt eq_elt} ls (m : t elt)
        (R0 := eq)
        (R1 := @M.eq_key_elt _)
        (HND : NoDupA (@eq_key _) ls)
  : (forall x, InA R1 x ls <-> InA R1 x (M.elements m))
    <-> M.Equiv R0 (from_internal_elements ls) m.
  Proof.
    unfold M.Equiv, M.In; subst R0 R1.
    repeat (split || intro);
      repeat match goal with
               | [ H : _ |- _ ]
                 => setoid_rewrite (@InA_from_internal_elements_2 : forall a b c d, impl _ _) in H
               | [ H : appcontext[M.MapsTo _ _ (from_internal_elements ?ls)] |- _ ]
                 => setoid_rewrite <- (@InA_from_internal_elements_1 _ ls _ _ HND : impl _ _) in H
               | _ => progress split_iff
               | _ => progress destruct_head ex
               | _ => progress destruct_head prod
               | [ H : forall a : prod _ _, _ |- _ ] => specialize (fun a b => H (a, b))
               | [ H : _ |- _ ] => setoid_rewrite <- (M.elements_1 : forall a b c d, impl _ _) in H
               | [ H : _ |- _ ] => setoid_rewrite (M.elements_2 : forall a b c d, impl _ _) in H
               | [ |- exists e, M.MapsTo ?k e (from_internal_elements ?ls) ]
                 => setoid_rewrite <- (@InA_from_internal_elements_1 _ ls k _ HND : impl _ _)
               | [ |- InA _ _ (M.elements _) ]
                 => apply M.elements_1
             end;
      eauto;
      split_ex_in_hyps;
      repeat match goal with
               | [ H : forall a b c, InA _ _ _ -> _, H' : InA _ _ _ |- _ ]
                 => specialize (H _ _ _ H')
               | [ H : forall a b c d e, InA _ _ _ -> _, H' : InA _ _ _ |- _ ]
                 => specialize (fun x y => H _ _ _ x y H')
               | [ H : forall a b, M.MapsTo _ _ _ -> _, H' : M.MapsTo _ _ _ |- _ ]
                 => specialize (H _ _ H')
               | [ H : forall a b c, M.MapsTo _ _ _ -> _, H' : M.MapsTo _ _ _ |- _ ]
                 => specialize (H _ _ _ H')
               | _ => progress destruct_head ex
               | _ => progress destruct_head prod
             end;
      try match goal with
            | [ H : InA ?R ?k ?ls, H' : InA ?R' ?k' ?ls |- _ ]
              => unique pose proof (@InA_NoDupA_eq_fine_0 _ R R' _ _ _ _ _ _ H H' HND)
          end;
      repeat match goal with
               | [ H : (forall a b, _ -> _) -> _ |- _ ] => specialize (H (fun a b H' => E.eq_sym (proj1 H')))
               | [ H : (forall a b, _ -> _) -> _ |- _ ] => specialize (H (fun a b H' => proj1 H'))
               | [ H : _ -> _ |- _ ] => specialize (H (reflexivity _))
               | _ => progress destruct_head ex
               | _ => progress unfold M.eq_key_elt in *
               | _ => progress simpl in *
               | _ => cleanup
             end.
  Qed.

  Local Ltac t_adj_misc_end :=
    eexists; split; [ | eassumption ];
    repeat esplit; simpl;
    eauto.

  Local Ltac t_adj_misc :=
    repeat esplit;
    eapply M.elements_2;
    apply InA_alt;
    t_adj_misc_end.

  Local Ltac t_adj_misc' :=
    repeat match goal with
             | [ H : E.eq ?x ?y |- _ ]
               => unique pose proof (E.eq_sym H)
             | [ x : key |- _ ]
               => unique pose proof (E.eq_refl x)
             | [ H : E.eq ?x ?y, H' : E.eq ?y ?z |- _ ]
               => unique pose proof (E.eq_trans H H')
             | [ H : E.eq ?k' ?k, H' : List.In (?k, ?v) ?ls |- _ ]
               => unique pose proof (proj2 (@InA_alt _ (@M.eq_key_elt _) (k', v) ls) (ex_intro _ (k, v) (conj (conj H (reflexivity _)) H')))
             | [ H : InA _ _ (M.elements _) |- _ ]
               => unique pose proof (M.elements_2 H)
             | [ H : M.MapsTo ?x ?e ?m |- _ ]
               => unique pose proof (M.find_1 H)
           end;
    cleanup.

  Local Ltac t_adj_destruct :=
    repeat match goal with
             | [ H : _ |- _ ] => setoid_rewrite InA_alt in H
             | _ => setoid_rewrite InA_alt
             | _ => progress split_ex_in_hyps
             | _ => progress destruct_head ex
             | _ => progress destruct_head_hnf and
             | _ => progress destruct_head prod
             | _ => progress destruct_head False
             | _ => progress subst
             | _ => progress hnf in *
             | _ => progress simpl in *
             | [ H : (_, _) = (_, _) |- _ ] => (inversion H; clear H)
             | [ H : appcontext[_ /\ List.In _ _] |- _ ]
               => edestruct H; clear H; [ repeat exists; hnf; simpl | eassumption | ]; simpl; try reflexivity; []
             | [ H : appcontext[exists e, M.MapsTo _ _ _] |- _ ]
               => edestruct H; clear H; [ repeat exists; hnf; simpl | eassumption | ]; simpl; try reflexivity; []
             | [ H : appcontext[_ /\ List.In _ _] |- _ ]
               => edestruct H; clear H; [ solve [ t_adj_misc ] | ]
           end.

  Local Ltac t_adj_specialize :=
    repeat match goal with
             | [ H : forall a b c d e f, _ -> ?T _ _ _ -> _, H' : ?T _ _ _ |- _ ]
               => specialize (fun a b c d e k => H a b c d e _ k H')
             | [ H : forall a b c d e f, _ -> ?T _ _ _ -> _, H' : ?T _ _ _ |- _ ]
               => specialize (fun a b c k => H a b c _ _ _ k H')
             | [ H : forall a b c d e, _ -> ?T _ _ _ -> _, H' : ?T _ _ _ |- _ ]
               => specialize (fun b c k => H _ b c _ _ k H')
             | [ H : forall a b c, ?T _ _ _ -> _, H' : ?T _ _ _ |- _ ]
               => specialize (H _ _ _ H')
             | [ H : forall b c, _ -> _ |- _ ]
               => specialize (H _ _ (reflexivity _))
             | [ H : forall a b c, _ -> _ |- _ ]
               => specialize (H _ _ _ (reflexivity _))
           end.

  Lemma adj_elements' {elt} eq_elt `{Equivalence elt eq_elt} ls (m : t elt)
        (R0 := (eq * option_lift_relation eq_elt)%signature)
        (R1 := (E.eq * R0)%signature)
        (HND : NoDupA (@eq_key _) ls)
  : (forall x, InA R1 x ls <-> InA R1 x (M.elements m))
    <-> M.Equiv R0 (from_internal_elements ls) m.
  Proof.
    unfold M.Equiv, M.In; subst R0 R1.
    repeat (split || intro);
      repeat match goal with
               | [ H : _ |- _ ]
                 => setoid_rewrite (@InA_from_internal_elements_2 : forall a b c d, impl _ _) in H
               | [ H : appcontext[M.MapsTo _ _ (from_internal_elements ?ls)] |- _ ]
                 => setoid_rewrite <- (@InA_from_internal_elements_1 _ ls _ _ HND : impl _ _) in H
               | _ => progress split_iff
               | _ => progress destruct_head ex
               | _ => progress destruct_head prod
               | [ H : forall a : prod _ _, _ |- _ ] => specialize (fun a b => H (a, b))
               | [ H : _ |- _ ] => setoid_rewrite <- (M.elements_1 : forall a b c d, impl _ _) in H
               | [ H : _ |- _ ] => setoid_rewrite (M.elements_2 : forall a b c d, impl _ _) in H
               | [ |- exists e, M.MapsTo ?k e (from_internal_elements ?ls) ]
                 => setoid_rewrite <- (@InA_from_internal_elements_1 _ ls k _ HND : impl _ _)
               | [ |- InA _ _ (M.elements _) ]
                 => apply M.elements_1
             end;
      eauto;
      t_adj_destruct.
    { repeat first [ progress t_adj_specialize
                   | progress t_adj_destruct ].
      t_adj_misc. }
    { match goal with
        | [ H : M.MapsTo ?x ?e ?m |- _ ]
          => atomic m; unique pose proof (M.elements_1 H)
      end;
      repeat first [ progress t_adj_specialize
                   | progress t_adj_destruct ].
      eexists; t_adj_misc_end. }
    { repeat first [ progress t_adj_specialize
                   | progress t_adj_destruct ].
      t_adj_misc'. }
    { t_adj_specialize.
      t_adj_destruct.
      t_adj_misc'. }
    { match goal with
        | [ H : M.MapsTo ?x ?e ?m |- _ ]
          => atomic m; unique pose proof (M.elements_1 H)
      end;
      repeat first [ progress t_adj_specialize
                   | progress t_adj_destruct ].
      t_adj_misc_end.
      t_adj_destruct; destruct_head option;
      trivial; t_adj_destruct.
      { etransitivity; eauto. }
      { etransitivity; eauto. } }
    { match goal with
        | [ H : M.MapsTo ?x ?e ?m |- _ ]
          => atomic m; unique pose proof (M.elements_1 H)
      end;
      repeat first [ progress t_adj_specialize
                   | progress t_adj_destruct ];
      t_adj_misc'.
      repeat match goal with
               | [ H : ?x = ?y, H' : ?y = ?x |- _ ] => atomic y; clear H
               | _ => progress subst
             end.
      t_adj_misc_end.
      lazy.
      destruct_head option; trivial;
      destruct_head False.
      { etransitivity; eauto.
        symmetry; eauto. } }
  Qed.

  Lemma adj_elements_equiv {elt} eq_elt `{Equivalence elt eq_elt} ls (m : t elt)
        (HND : NoDupA (@eq_key _) ls)
  : equivlistA (E.eq * (eq * option_lift_relation eq_elt))%signature
                     ls
                     (M.elements m)
    <-> M.Equiv (eq * option_lift_relation eq_elt)%signature (from_internal_elements ls) m.
  Proof.
    apply adj_elements'; eauto.
  Qed.

  Lemma eqlistA_equivlistA {A} {R R' : relation A} `{Transitive A R'}
        (H0 : forall x y, R x y -> R' x y)
        (H1 : forall x y, R x y -> R' y x)
        (ls ls' : list A)
  : eqlistA R ls ls' -> equivlistA R' ls ls'.
  Proof.
    unfold equivlistA in *.
    revert ls'.
    induction ls; intros ls' H'; inversion H'; subst; clear H';
    hnf; intro x; split; try tauto;
    intro H''; inversion H''; subst; clear H'';
    try solve [ left; etransitivity; eauto
              | split_iff; right; eauto ].
  Qed.

  Lemma NoDupA_eqlistA {A} {R R' : relation A} `{Equivalence A R'} ls ls'
        (H' : forall x y : A, R x y -> R' x y)
        (H'' : forall x y : A, R x y -> R' y x)
        (HD : NoDupA R' ls')
        (HE : eqlistA R ls ls')
  : NoDupA R' ls.
  Proof.
    revert ls HE; induction ls'; intros ls HE;
    inversion HE; subst; clear HE;
    inversion HD; subst; clear HD;
    trivial.
    constructor; eauto.
    repeat match goal with
             | _ => intro
             | [ H : ~_ |- _ ] => apply H; clear H
             | _ => eassumption
             | [ H : _ |- _ ] => rewrite <- H; []
             | [ H : _ |- _ ] => rewrite (H'' _ _ H); []
             | [ H : _ |- _ ] => apply eqlistA_equivlistA in H4; unfold Equivalence.equiv in *; eauto; []
           end.
  Qed.

  Lemma adj_elements_1 {elt} eq_elt `{Equivalence elt eq_elt} ls (m : t elt)
  : eqlistA (E.eq * (eq * option_lift_relation eq_elt))%signature
                     ls
                     (M.elements m)
    -> M.Equiv (eq * option_lift_relation eq_elt)%signature (from_internal_elements ls) m.
  Proof.
    intro H'.
    rewrite <- adj_elements_equiv; trivial.
    { intros; eapply eqlistA_equivlistA; eauto.
      intros; symmetry; trivial. }
    { assert (Equivalence
                (E.eq *
                 (@eq nat * option_lift_relation eq_elt)%signature))
        by (split; typeclasses eauto).
      assert (Equivalence (eq_key (elt:=nat * option elt)))
        by (split; typeclasses eauto).
      eapply NoDupA_eqlistA;
        try first [ eassumption
                  | apply M.elements_3w ];
      unfold eq_key; intros; destruct_head_hnf and; hnf in *;
      destruct_head prod;
      eauto. }
  Qed.

  Lemma adj_elements_2 {elt} eq_elt `{Equivalence elt eq_elt} ls (m : t elt)
        (H' : Sorted (@M.lt_key _) ls)
  : M.Equiv (eq * option_lift_relation eq_elt)%signature (from_internal_elements ls) m
    -> eqlistA (E.eq * (eq * option_lift_relation eq_elt))%signature
               ls
               (M.elements m).
  Proof.
    pose proof (SortA_NoDupA _ _ _ H') as HND.
    rewrite <- adj_elements_equiv; trivial.
    pose proof (M.elements_3 m).
    eapply SortA_equivlistA_eqlistA;
      try eassumption;
      try typeclasses eauto.
    { split; typeclasses eauto. }
  Qed.

  Lemma MEquiv_Equiv {elt} (eq_elt : relation elt) m1 m2
  : M.Equiv (eq * option_lift_relation eq_elt)%signature m1 m2
    -> Equiv eq_elt m1 m2.
  Proof.
    unfold Equiv, M.Equiv, In, M.In, MapsTo.
    repeat match goal with
             | _ => intro
             | _ => progress cleanup
             | _ => progress simpl in *
             | _ => progress split_iff
             | _ => progress destruct_head ex
             | _ => progress destruct_head option
             | _ => progress destruct_head_hnf and
             | _ => progress split_ex_in_hyps
             | _ => progress hnf in *
             | _ => solve [ repeat esplit; eassumption ]
             | [ H : M.MapsTo _ _ _, H' : forall a b, M.MapsTo _ _ _ -> _ |- _ ]
               => specialize (H' _ _ H)
             | [ H : M.MapsTo _ _ _, H' : forall a b c, M.MapsTo _ _ _ -> _ |- _ ]
               => specialize (H' _ _ _ H)
             | [ H : M.MapsTo _ _ _, H' : forall a b c d e, M.MapsTo _ _ _ -> _ |- _ ]
               => specialize (fun d e => H' _ _ _ d e H)
             | [ H : M.MapsTo _ _ _, H' : forall a b c d e f, M.MapsTo _ _ _ -> _ |- _ ]
               => specialize (fun d e f => H' _ _ _ d e f H)
           end;
    add_facts; cleanup.
  Qed.

  Lemma from_to_string_map {elt}
        (eq_elt : relation elt)
        `{Equivalence elt eq_elt, PrefixSerializable elt eq_elt}
  : forall x : t elt,
      option_lift_relation (Equiv eq_elt) (fst (from_string (A := t elt) (to_string x))) (Some x)
      /\ snd (from_string (A := t elt) (to_string x)) = ""%string.
  Proof.
    intros; simpl; unfold id.
    set (R := (eqlistA (E.eq * (eq * (option_lift_relation eq_elt)))%signature) : relation (list (M.key * (nat * option elt)))).
    split.
    { unfold sorted_from_internal_elements.
      simpl.
      pose proof (@from_to_string_1 _ R _ (M.elements x)).
      pose proof (M.elements_3 x).
      repeat match goal with
               | _ => intro
               | _ => progress cleanup
               | _ => progress unfold option_map in *
               | _ => progress simpl in *
               | [ H : is_sorted _ = false |- _ ] => apply not_Sorted_is_sorted in H
               | [ H : R ?x ?y, H' : Sorted _ ?y |- _ ]
                 => unique pose proof (proj2 (Sorted_eqlistA H) H')
               | [ H : R ?x ?y, H' : Sorted _ ?x |- _ ]
                 => unique pose proof (proj1 (Sorted_eqlistA H) H')
               | [ |- appcontext[match ?E with _ => _ end] ]
                 => case_eq E
               | [ H : ?x = @None ?T, H' : appcontext G[?x] |- _ ]
                 => let G' := context G[@None T] in
                    assert G' by (rewrite <- H; exact H');
                      clear H'
               | [ H : ?x = Some ?y, H' : appcontext G[?x] |- _ ]
                 => let G' := context G[Some y] in
                    assert G' by (rewrite <- H; exact H');
                      clear H'
               | _ => solve [ eauto using MEquiv_Equiv, adj_elements_1 ]
             end. }
    { assert (H' := @from_to_string_2 _ R _).
      apply H'. }
  Qed.

  Lemma prefix_closed_map_strict {elt}
        (eq_elt : relation elt)
        `{Equivalence elt eq_elt, PrefixSerializable elt eq_elt}
        (R0 := (eq * (option_lift_relation eq_elt))%signature)
  : forall s1 s2 x,
      option_lift_relation (M.Equiv R0) (fst (from_string (A := t elt) s1)) (Some x)
      -> option_lift_relation (M.Equiv R0) (fst (from_string (A := t elt) (s1 ++ s2))) (Some x)
         /\ snd (from_string (A := t elt) (s1 ++ s2)) = (snd (from_string (A := t elt) s1) ++ s2)%string.
  Proof.
    simpl; unfold id.
    set (R := eqlistA (E.eq * R0)%signature).
    assert (Reflexive R) by (subst R; typeclasses eauto).
    intros s1 s2 x; split; simpl in *;
    [ assert (H' := @prefix_closed_1 _ R _ s1 s2)
    | assert (H' := @prefix_closed_2 _ R _ s1 s2 (M.elements x)) ];
    repeat match goal with
             | _ => progress unfold option_map, option_lift_relation in *
             | _ => progress cleanup
             | _ => progress simpl in *
             | [ H : appcontext[match ?E with _ => _ end] |- _ ]
               => revert H; case_eq E; intros
             | [ |- appcontext[match ?E with _ => _ end] ]
               => case_eq E; intros
             | [ H : ?x = @None ?T, H' : appcontext G[?x] |- _ ]
               => let G' := context G[@None T] in
                  assert G' by (rewrite <- H; exact H');
                    clear H'
             | [ H : ?x = Some ?y, H' : appcontext G[?x] |- _ ]
               => let G' := context G[Some y] in
                  assert G' by (rewrite <- H; exact H');
                    clear H'
             | [ H : ?x = Some ?y |- appcontext G[?x] ]
               => let G' := context G[Some y] in
                  let H' := fresh in
                  assert (H' : G');
                    [ | rewrite <- H in H'; exact H' ];
                    simpl
             | _ => eapply H'; clear H'
             | _ => solve [ subst R; eauto ]
             | _ => solve [ subst R; eauto using adj_elements_2, adj_elements_1 ]
             | [ H : is_sorted _ = false |- _ ] => apply not_Sorted_is_sorted in H
             | [ H : is_sorted _ = true |- _ ] => apply Sorted_is_sorted in H
             | [ H : R ?x ?y, H' : Sorted _ ?y |- _ ]
               => unique pose proof (proj2 (Sorted_eqlistA H) H')
             | [ H : R ?x ?y, H' : Sorted _ ?x |- _ ]
               => unique pose proof (proj1 (Sorted_eqlistA H) H')
             | [ H : forall _, R _ _ -> R _ _ |- _ ]
               => unique pose proof (H' _ (reflexivity _))
             | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
           end.
  Qed.

  Lemma prefix_closed_map {elt}
        (eq_elt : relation elt)
        `{Equivalence elt eq_elt, PrefixSerializable elt eq_elt}
  : forall s1 s2 x,
      option_lift_relation (Equiv eq_elt) (fst (from_string (A := t elt) s1)) (Some x)
      -> option_lift_relation (Equiv eq_elt) (fst (from_string (A := t elt) (s1 ++ s2))) (Some x)
         /\ snd (from_string (A := t elt) (s1 ++ s2)) = (snd (from_string (A := t elt) s1) ++ s2)%string.
  Proof.
    intros s1 s2 x.
    pose proof (@prefix_closed_map_strict elt eq_elt _ _ s1 s2).
    repeat match goal with
             | _ => progress unfold option_lift_relation
             | _ => progress unfold id in *
             | [ H : ?x = Some _, H' : appcontext[?x] |- _ ] => rewrite H in H'
             | [ H : ?x = None, H' : appcontext[?x] |- _ ] => rewrite H in H'
             | _ => progress simpl in *
             | [ H : appcontext[match ?E with _ => _ end] |- _ ]
               => revert H; case_eq E; intros
             | [ |- appcontext[match ?E with _ => _ end] ]
               => case_eq E; intros
             | [ H : forall x, M.Equiv _ _ _ -> _ |- _ ]
               => specialize (H _ (reflexivity _))
             | _ => progress split_and
             | [ H : False |- _ ] => destruct H
             | [ H : M.Equiv _ _ _ |- _ ] => apply MEquiv_Equiv in H
             | [ |- _ /\ _ ] => split; eauto; []
             | _ => solve [ etransitivity; eauto ]
           end.
  Qed.

  Definition PrefixSerializable_map {elt} {eq_elt} `{Equivalence elt eq_elt, PrefixSerializable elt eq_elt}
  : PrefixSerializable (t elt) (Equiv eq_elt)
    := {| serialize := _;
          deserialize := _;
          from_to_string := @from_to_string_map elt eq_elt _ _;
          prefix_closed := @prefix_closed_map elt eq_elt _ _ |}.
End MakeSerializableMergableMap.
