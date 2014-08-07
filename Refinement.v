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
End Refinement.

Ltac refines := repeat (apply refines_refl || apply done_left || apply done_right
                              || apply recv_recv || apply match_right; intros).
