Require Import Process Refinement List Eqdep_dec.


Ltac normalize := repeat (solve [ apply normProcD | eapply normBasic; repeat (constructor; intros) ]
                       || eapply normParallel).

Ltac inverter H := let H' := fresh "H'" in
                   generalize H; intro H'; apply (f_equal (@Chans _)) in H'; simpl in H'; subst;
                   apply (f_equal (@Code _)) in H; simpl in H; subst.

Definition channelOf {chs} (p : proc0 chs) :=
  match p with
  | NSend ch _ _ => ch
  | NRecv ch _ => ch
  | NDone => ""
  end.

Inductive simplified {chs} (ch : string) : Type :=
| SSend (v : chs ch) (k : proc0 chs)
| SRecv (k : chs ch -> proc0 chs)
| SDone.

Definition simplify {chs} (p : proc0 chs) : simplified (channelOf p) :=
  match p with
  | NSend _ v k => SSend _ v k
  | NRecv _ k => SRecv _ k
  | NDone => SDone _
  end.

Require Import Eqdep_dec.

Ltac inverter2 H := let H' := fresh "H'" in generalize H; intro H';
                    apply (f_equal (@channelOf _)) in H'; simpl in H'; subst;
                    apply (f_equal (fun x => existT simplified (channelOf x) (simplify x))) in H;
                    simpl in H; apply (inj_pair2_eq_dec _ string_dec) in H; inv H.

Ltac oneStep0 :=
  match goal with
  | _ => discriminate
  | [ H : _ :: _ = _ :: _ |- _ ] => 
    inversion H; clear H; intros;
    repeat match goal with
                                  | [ x : _ |- _ ] => subst x
                                  | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
                                    apply (inj_pair2_eq_dec _ string_dec) in H; subst
           end
  | [ H : pick1 ?ls _ _ |- _ ] => remember ls; inv H

  | [ H : Build_proc _ _ _ = Build_proc _ _ _ |- _ ] => inverter H
  | [ H : NSend _ _ _ _ = NSend _ _ _ _ |- _ ] => inverter2 H
  | [ H : NRecv _ _ _ = NRecv _ _ _ |- _ ] => inverter2 H
  end.

Ltac oneStep' := simpl; intros; repeat oneStep0.

Ltac oneStep :=
  apply oneStep; oneStep'.

Ltac picker' ls toHere k :=
  match ls with
  | _ :: ?ls' =>
    k ltac:(toHere; apply Fst1)
    || picker' ls' ltac:(toHere; apply More1) k
  end.

Ltac picker :=
  match goal with
  | [ |- exists P k ps', pick1 ?ls _ _ /\ P _ /\ refines _ _ ] =>
    picker' ls idtac ltac:(fun tac => do 4 esplit; [ tac | split; [ simpl; tauto | ] ])
  end.

Ltac refines := eapply refines_normalize; [ normalize | normalize | oneStep; try picker ].

Module DoneDone.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := Done.

  Definition pr2 : process chs := Done.

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
  Qed.
End DoneDone.

Module DoneSend.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := Done.

  Definition pr2 : process chs := #!chs["X", 0], Done.

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
  Qed.
End DoneSend.

Module SendSend.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := #!chs["X", 0], Done.

  Definition pr2 : process chs := #!chs["X", 0], Done.

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
    refines.
  Qed.
End SendSend.
