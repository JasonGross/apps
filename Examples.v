Require Import Process Refinement.


Ltac normalize := solve [ eapply normBasic; repeat (constructor; intros) ].

Ltac oneStep :=
  apply oneStep; simpl; intros;
  repeat match goal with
         | [ H : pick1 _ _ _ |- _ ] => inv H
         end.

Module DoneDone.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := Done.

  Definition pr2 : process chs := Done.

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    eapply refines_normalize.
    normalize.
    normalize.
    oneStep.
  Qed.
End DoneDone.
