Require Import List Process Eqdep_dec.


Ltac inv H := inversion H; clear H; subst;
              repeat match goal with
                     | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
                       apply (inj_pair2_eq_dec _ string_dec) in H; subst
                     end.

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

  Lemma interleave_sym : forall tr1 tr2 tr3,
    interleave (chs := chs) tr1 tr2 tr3
    -> interleave tr2 tr1 tr3.
  Proof.
    induction 1; eauto.
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

  Theorem normSend : forall ch v k p,
    norm k (p :: nil)
    -> Chans p (Send, ch)
    -> norm (DoSend ch v k) ({| Chans := Chans p; Code := NSend ch v (Code p) |} :: nil).
  Proof.
    unfold norm, refines; simpl; intuition.

    inv H; eauto.
    apply H1 in H7; clear H1.
    inv H7; eauto.
    inv H4.
    apply interleave_sym in H6; apply interleave_nil1 in H6; subst.
    unfold procD in *; simpl in *.
    inv H3; eauto.
    econstructor.
    2: eauto.
    2: eauto.
    econstructor.
    rewrite (expand_ok (proc0D (NSend ch v (Code p)))); simpl.
    eauto.
    eauto.
    econstructor.
    2: eauto.
    2: eauto.
    econstructor.
    rewrite (expand_ok (proc0D (NSend ch v (Code p)))); simpl.
    eauto.
    eauto.
    econstructor.
    2: eauto.
    2: eauto.
    econstructor.
    simpl.
    rewrite (expand_ok (proc0D (NSend ch v (Code p)))); simpl.
    eauto.
    eauto.

    unfold procD in *; simpl in *.
    inv H; eauto.
    inv H6.
    apply interleave_sym in H8; apply interleave_nil1 in H8; subst.
    inv H5; eauto.
    rewrite (expand_ok (proc0D (NSend ch v (Code p)))) in *.
    simpl in *.
    inv H4; eauto.
    econstructor; eauto.
    apply H2.
    inv H7; eauto.
  Qed.
End Refinement.
