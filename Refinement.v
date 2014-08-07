Require Import Process Eqdep_dec.


Ltac inv H := inversion H; clear H; subst;
              repeat match goal with
                     | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
                       apply (inj_pair2_eq_dec _ string_dec) in H; subst
                     end.

Section Refinement.
  Variable chs : channels.

  Theorem refines_refl : forall k,
    refines (chs := chs) k k.
  Proof.
    intros; hnf; eauto.
  Qed.

  Theorem done_left : forall k,
    refines (chs := chs) Done k.
  Proof.
    intros; hnf; intros.
    inv H; eauto.
  Qed.

  Theorem done_right : forall k k',
    refines k k'
    -> refines (chs := chs) k (Done || k').
  Proof.
    intros; hnf; intros.
    apply H in H0; firstorder.
    eexists; split.
    econstructor.
    eauto.
    eauto.
    eauto.
    auto.
  Qed.

  Theorem recv_recv : forall ch k k' k'',
    (forall v, refines (k v) (k' v || k''))
    -> refines (DoRecv (chs := chs) ch k) (DoRecv ch k' || k'').
  Proof.
    intros; hnf; intros.
    inv H0; eauto.

    apply H in H4; firstorder.
    eexists; split.
    inv H0.
    econstructor.
    econstructor.
    eauto.
    eauto.
    econstructor; eauto.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.
  Qed.

  Lemma traceEqual_interleave : forall tr tr',
    traceEqual (chs := chs) tr' tr
    -> forall tr1 tr2, interleave tr1 tr2 tr
    -> interleave tr1 tr2 tr'.
  Proof.
    cofix; destruct 2.

    destruct H.
    constructor.
    econstructor; eauto.

    destruct H.
    constructor.
    econstructor; eauto.

    inv H.
    eauto.

    inv H.
    eauto.

    eauto.
    eauto.
  Qed.

  Hint Immediate traceEqual_interleave.

  Theorem recv_recv_restricted : forall (which : direction * channel -> Prop) ch k k' k'',
    which (Recv, ch)
    -> (forall v, refines (k v) (Restrict which (k' v) || k''))
    -> refines (DoRecv (chs := chs) ch k) (Restrict which (DoRecv ch k') || k'').
  Proof.
    intros; hnf; intros.
    inv H1; eauto.

    apply H0 in H5; clear H0; firstorder.
    inv H0.
    Focus 2.

    inv H1.
    eexists; split.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.

    inv H4.
    Focus 2.
    eexists; split.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.
    2: eauto.
    eauto.

    eexists; split.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.
    eauto.
    econstructor; eauto.
    eauto.
  Qed.

  Theorem match_right : forall ch k k' k'' v,
    refines k (k' || k'' v)
    -> refines (chs := chs) k (DoSend ch v k' || DoRecv ch k'').
  Proof.
    intros; hnf; intros.
    apply H in H0; firstorder.
    inv H0; subst.
    Focus 2.
    inv H1; eauto.

    eexists; split.
    econstructor.
    econstructor.
    eauto.
    econstructor.
    eauto.
    eauto.
    auto.
  Qed.

  Lemma interleave_nil1 : forall tr1 tr2,
    interleave (chs := chs) SNil tr1 tr2
    -> traceEqual tr1 tr2.
  Proof.
    cofix; inversion 1; subst; intros.
    eauto.
    eauto.
    constructor; eauto.
  Qed.

  Lemma traceEqual_sym : forall tr1 tr2,
    traceEqual (chs := chs) tr1 tr2
    -> traceEqual tr2 tr1.
  Proof.
    cofix; destruct 1; econstructor; eauto.
  Qed.

  Lemma traceEqual_trans : forall tr1 tr2 tr3,
    traceEqual (chs := chs) tr1 tr2
    -> traceEqual tr2 tr3
    -> traceEqual tr1 tr3.
  Proof.
    cofix; destruct 1; inversion 1; econstructor; eauto.
  Qed.

  Theorem match_right_restricted : forall (which : _ -> Prop) ch k k' k'' v,
    which (Send, ch)
    -> refines k (Restrict which k' || k'' v)
    -> refines (chs := chs) k (Restrict which (DoSend ch v k') || DoRecv ch k'').
  Proof.
    intros; hnf; intros.
    apply H0 in H1; clear H0; firstorder.
    inv H0; subst.
    Focus 2.
    inv H1; eauto.

    inv H4.
    Focus 2.
    apply interleave_nil1 in H7.
    eexists; split.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.
    econstructor.
    eauto.
    eauto.
    eauto using traceEqual_trans, traceEqual_sym.

    eexists; split.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.
    econstructor; eauto.
    eauto.
    auto.
  Qed.

  Theorem send_send : forall ch k k' k'' v,
    refines k (k' || k'')
    -> refines (DoSend (chs := chs) ch v k) (k' || DoSend ch v k'').
  Proof.
    intros; hnf; intros.
    inv H0; eauto.
    apply H in H5; clear H; firstorder.
    inv H.
    Focus 2.

    inv H0.
    eexists; split.
    econstructor.
    eauto.
    econstructor.
    eauto.
    eauto.
    eauto.

    eexists; split.
    econstructor.
    eauto.
    econstructor.
    eauto.
    econstructor; eauto.
    eauto.
  Qed.

  Theorem done_right_restricted : forall which k k',
    refines k k'
    -> refines (chs := chs) k (Restrict which Done || k').
  Proof.
    intros; hnf; intros.
    apply H in H0; firstorder.
    eexists; split.
    econstructor.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    auto.
  Qed.
End Refinement.

Ltac refines := repeat (apply refines_refl || apply done_left || apply done_right
                              || apply recv_recv || apply match_right; intros).
