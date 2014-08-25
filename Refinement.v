Require Import List Process Eqdep_dec.


Ltac inv H := inversion H; clear H; subst;
              repeat match goal with
                     | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
                       apply (inj_pair2_eq_dec _ string_dec) in H; subst
                     end; simpl in *.

Section Refinement.
  Variable chs : channels.

  (** A normal form for processes *)

  CoInductive proc0 :=
  | NSend (ch : channel) (v : chs ch) (k : proc0)
  | NRecv (ch : channel) (k : chs ch -> proc0)
  | NDone.

  Record proc := {
    Chans : direction * channel -> Prop;
    Code : proc0
  }.

  Definition procs := list proc.

  CoFixpoint proc0D (p : proc0) : process chs :=
    match p with
    | NSend ch v k => DoSend ch v (proc0D k)
    | NRecv ch k => DoRecv ch (fun v => proc0D (k v))
    | NDone => Done
    end.

  Definition procD (p : proc) : process chs :=
    Restrict (Chans p) (proc0D (Code p)).

  Fixpoint procsD (ps : procs) : process chs :=
    match ps with
    | nil => Done
    | p :: ps' => Parallel (procD p) (procsD ps')
    end.

  Definition norm (p : process chs) (ps : procs) : Prop :=
    refines p (procsD ps)
    /\ refines (procsD ps) p.

  CoInductive normalize : process chs -> proc0 -> Prop :=
  | InSend : forall ch v k k', normalize k k'
    -> normalize (DoSend ch v k) (NSend ch v k')
  | InRecv : forall ch k k', (forall v, normalize (k v) (k' v))
    -> normalize (DoRecv ch k) (NRecv ch k')
  | InDone : normalize Done NDone.

  Lemma expand_proc0D : forall p, proc0D p = expand (proc0D p).
  Proof.
    intros.
    rewrite <- expand_ok.
    auto.
  Qed.

  Lemma normalize_fwd : forall p tr, traceOf p tr
    -> forall p', normalize p p'
      -> traceOf (proc0D p') tr.
  Proof.
    induction 1; simpl; eauto; inversion 1; subst.
    apply (inj_pair2_eq_dec _ string_dec) in H3; subst.
    rewrite expand_proc0D in *; simpl in *.
    eauto.
    apply (inj_pair2_eq_dec _ string_dec) in H3; subst.
    rewrite expand_proc0D in *; simpl in *.
    eauto.
  Qed.


  Lemma normalize_bwd : forall p'0 tr, traceOf p'0 tr
    -> forall p p', normalize p p'
      -> p'0 = proc0D p'
      -> traceOf p tr.
  Proof.
    induction 1; simpl; eauto; destruct 1; simpl; intros;
    try match goal with
        | [ H : _ = proc0D _ |- _ ] => rewrite expand_proc0D in H; simpl in H; inv H; eauto
        end.

    rewrite expand_proc0D in *; simpl in *.
    inversion H1; clear H1.
    destruct H3.
    apply (inj_pair2_eq_dec _ string_dec) in H4; subst.
    eauto.
  Qed.

  Lemma traceAll_True : forall p, traceAll (chs := chs) (fun _ => True) p.
  Proof.
    induction p; auto.
  Qed.

  Hint Resolve traceAll_True.

  Lemma interleave_nil1' : forall nl tr1 tr2,
    interleave (chs := chs) nl tr1 tr2
    -> nl = nil
    -> tr1 = tr2.
  Proof.
    induction 1; simpl; intros; intuition; try congruence.
  Qed.

  Lemma interleave_nil1 : forall tr1 tr2,
    interleave (chs := chs) nil tr1 tr2
    -> tr1 = tr2.
  Proof.
    eauto using interleave_nil1'.
  Qed.

  Lemma interleave_sym : forall tr1 tr2 tr3,
    interleave (chs := chs) tr1 tr2 tr3
    -> interleave tr2 tr1 tr3.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma interleave_nil2 : forall tr1 tr2,
    interleave (chs := chs) tr1 nil tr2
    -> tr1 = tr2.
  Proof.
    intros; apply interleave_nil1; apply interleave_sym; auto.
  Qed.

  Theorem normBasic : forall p p', normalize p p'
    -> norm p ({| Chans := fun _ => True; Code := p' |} :: nil).
  Proof.
    split; unfold procsD, procD; simpl.

    do 2 intro.
    econstructor.
    2: eauto.
    2: eauto.
    econstructor.
    eauto using normalize_fwd.
    auto.

    do 2 intro.
    inv H0; eauto.
    inv H4.
    apply interleave_nil2 in H6; subst.
    inv H3; eauto.
    eauto using normalize_bwd.
  Qed.

  Theorem normDone : norm Done ({| Chans := fun _ => True; Code := NDone |} :: nil).
  Proof.
    split; simpl; do 2 intro.
    eauto.
    inv H; eauto.
    inv H3; eauto.
    rewrite (expand_ok (procD
            {| Chans := fun _ : direction * channel => True; Code := NDone |})) in H2; simpl in H2.
    inv H2; eauto.
    rewrite (expand_ok (proc0D NDone)) in H1; simpl in H1.
    inv H1; eauto.
    inv H5; eauto.
    inv H5; eauto.
  Qed.

  Theorem Parallel_comm : forall p1 p2,
    refines (chs := chs) (p1 || p2) (p2 || p1).
  Proof.
    do 4 intro.
    inv H; eauto using interleave_sym.
  Qed.

  Ltac reassoc1 :=
    try match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
        end;
    try match goal with
        | [ IHinterleave : forall tr3 tr3 : trace chs, _, H : interleave _ _ _ |- _ ] =>
          apply IHinterleave in H; clear IHinterleave; firstorder
        end;
    try match goal with
        | [ H : _ = _ -> ex _ |- _ ] => destruct H; intuition; []
        end;
    try solve [ do 2 esplit; [ solve [ econstructor; eauto | apply IntCons2; eauto ] | eauto ] ].

  Ltac induct :=
    match goal with
    | [ H : interleave _ _ ?ls |- _ ] =>
      remember ls; induction H; subst; eauto; try congruence
    end.

  Ltac reassoc := solve [ reassoc1 ] || (induct; reassoc1).

  Lemma interleave_reassoc1 : forall tr3 tr tr',
    interleave (chs := chs) tr3 tr tr'
    -> forall tr1 tr2, interleave (chs := chs) tr1 tr2 tr
    -> exists tr'', interleave tr3 tr1 tr'' /\ interleave tr'' tr2 tr'.
  Proof.
    induction 1; eauto; intros; reassoc.
  Qed.

  Theorem Parallel_assoc1 : forall p1 p2 p3,
    refines (chs := chs) (p1 || (p2 || p3)) ((p1 || p2) || p3).
  Proof.
    do 5 intro.
    inv H; eauto.
    inv H3; eauto.
    eapply interleave_reassoc1 in H7; try apply H5; firstorder.
    eauto.
  Qed.

  Lemma interleave_reassoc2 : forall tr3 tr tr',
    interleave (chs := chs) tr tr3 tr'
    -> forall tr1 tr2, interleave (chs := chs) tr1 tr2 tr
    -> exists tr'', interleave tr2 tr3 tr'' /\ interleave tr1 tr'' tr'.
  Proof.
    induction 1; eauto; intros; reassoc.
  Qed.

  Theorem Parallel_assoc2 : forall p1 p2 p3,
    refines (chs := chs) ((p1 || p2) || p3) (p1 || (p2 || p3)).
  Proof.
    do 5 intro.
    inv H; eauto.
    inv H2; eauto.
    eapply interleave_reassoc2 in H7; try apply H5; firstorder eauto.
  Qed.

  Lemma procsD_app1 : forall ps2 ps1,
    refines (procsD (ps1 ++ ps2)%list) (Parallel (procsD ps1) (procsD ps2)).
  Proof.
    induction ps1; simpl; hnf; intros; eauto.
    apply Parallel_assoc1.
    inv H; eauto.
  Qed.

  Lemma procsD_app2 : forall ps2 ps1,
    refines (Parallel (procsD ps1) (procsD ps2)) (procsD (ps1 ++ ps2)%list).
  Proof.
    induction ps1; simpl; hnf; intros; eauto.

    inv H; eauto.
    inv H2; eauto.
    apply interleave_nil1 in H5; congruence.

    apply Parallel_assoc2 in H.
    inv H; eauto.
  Qed.

  Theorem normParallel : forall p1 ps1 p2 ps2, norm p1 ps1
    -> norm p2 ps2
    -> norm (Parallel p1 p2) (ps1 ++ ps2)%list.
  Proof.
    split; simpl; do 2 intro.

    apply procsD_app2.
    unfold norm, refines in *.
    intuition.
    inv H1; eauto.

    apply procsD_app1 in H1.
    unfold norm, refines in *.
    intuition.
    inv H1; eauto.
  Qed.

  Lemma traceAll_and : forall P1 P2 tr,
    traceAll (chs := chs) P1 tr
    -> traceAll P2 tr
    -> traceAll (fun x => P1 x /\ P2 x) tr.
  Proof.
    induction 1; inversion 1; subst; eauto.
    constructor; intuition.
  Qed.

  Lemma traceAll_weaken : forall (P1 P2 : _ -> Prop),
    (forall x, P1 x -> P2 x)
    -> forall ps, traceAll (chs := chs) P1 ps
      -> traceAll P2 ps.
  Proof.
    induction 2; eauto.
  Qed.

  Theorem normRestrict1 : forall (P : _ -> Prop) p p',
    norm p (p' :: nil)
    -> norm (Restrict P p) ({| Code := Code p';
                               Chans := fun x => P x /\ Chans p' x |} :: nil).
  Proof.
    unfold norm, refines, procsD, procD; simpl; intuition.

    inv H; eauto.
    apply H0 in H4; clear H0.
    inv H4; eauto.
    inv H3.
    apply interleave_nil2 in H7; subst.
    inv H2; eauto.
    econstructor.
    2: eauto.
    2: eauto.
    econstructor.
    eauto.
    auto using traceAll_and.

    inv H; eauto.
    inv H5.
    apply interleave_nil2 in H7; subst.
    inv H4; eauto.
    econstructor; eauto.
    apply H1.
    econstructor.
    2: eauto.
    2: eauto.
    2: eapply traceAll_weaken; [ | eassumption ]; cbv beta; tauto.
    econstructor.
    eauto.
    eapply traceAll_weaken; [ | eassumption ]; cbv beta; tauto.
  Qed.

  Lemma traceAll_interleave : forall tr1 tr2 tr, interleave (chs := chs) tr1 tr2 tr
    -> forall P, traceAll P tr1
      -> traceAll P tr2
      -> traceAll P tr.
  Proof.
    induction 1; inversion 1; subst; inversion 1; subst; eauto;
    econstructor; eauto; apply IHinterleave; eauto.
  Qed.

  Theorem normRestrictMany : forall (P : _ -> Prop) p ps,
    norm p ps
    -> Forall (fun r => forall x, Chans r x -> P x) ps
    -> norm (Restrict P p) ps.
  Proof.
    unfold norm, refines; intuition.

    inv H; eauto.

    econstructor.
    auto.
    clear H1 H2.
    generalize dependent tr.
    induction H0; simpl; intros.
    inv H; eauto.
    inv H1; eauto.
    unfold procD in H4.
    inv H4; eauto.
    eapply traceAll_interleave; eauto.
    eapply traceAll_weaken; eauto.

    apply interleave_nil1 in H7; subst.
    eauto.
  Qed.    

End Refinement.
