(** * Calculate how many more ticks are needed to wake up the tick box *)
Require Import Coq.Program.Basics Coq.NArith.NArith Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import TrustedTickBox.
Require Import Common.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope program_scope.
Local Open Scope N_scope.

Section howManyMoreTicksNeeded_correct.
  Lemma helper_1 (x y : N) : (x <=? y + (x - y)) = true.
  Proof.
    apply N.leb_le.
    repeat match goal with
             | [ x : N |- _ ] => rewrite <- (N2Nat.id x); generalize (N.to_nat x); intros; clear
             | _ => rewrite <- !Nat2N.inj_sub
             | _ => rewrite <- !Nat2N.inj_add
             | _ => rewrite <- !Nat2N.inj_compare
             | _ => rewrite <- !Compare_dec.nat_compare_gt
             | [ |- _ <= _ ] => hnf
             | _ => omega
           end.
  Qed.

  Lemma N_compare_antisym_helper {x y c} (H : (x ?= y) = c)
  : (y ?= x) = CompOpp c.
  Proof.
    rewrite N.compare_antisym in H; subst; destruct (y ?= x); reflexivity.
  Qed.

  Local Ltac t :=
    repeat match goal with
             | _ => reflexivity
             | _=> progress subst
             | _ => intro
             | [ H : ?x = ?x |- _ ] => clear H
             | [ |- _ /\ _ ] => split
             | [ H : ~?T, H' : ?T |- _ ] => specialize (H H')
             | [ H : ?T -> False, H' : ?T |- _ ] => specialize (H H')
             | [ H : False |- _ ] => solve [ destruct H ]
             | [ H : NotYetWaitingOnTicks = WillWaitForMoreTicks _ |- _ ] => solve [ inversion H ]
             | [ H : _ = _ :> TickBoxPreState _ |- _ ] => solve [ inversion H ]
             | [ H : true = false |- _ ] => solve [ inversion H]
             | [ H : false = true |- _ ] => solve [ inversion H]
             | [ H : _::_ = nil |- _ ] => solve [ inversion H ]
             | [ H : ?n < ?n |- _ ] => apply N.lt_irrefl in H
             | [ H : (?x <=? ?y) = true |- _ ] => apply N.leb_le in H
             | [ H : ?x <= ?y, H' : context[(?y - ?x) + ?x] |- _ ]
               => rewrite <- N.add_sub_swap in H' by assumption
             | _ => progress simpl in *
             | _ => progress unfold howManyMoreTicksNeeded, set_curData, readyToTransmit, readyToGetUpdate, ticksTooCoarseWaitingOnTicks in *
             | [ H : WillWaitForMoreTicks _ = WillWaitForMoreTicks _ |- _ ] => (inversion H; clear H)
             | [ H : WaitingOnData _ _ _ = WaitingOnData _ _ _ |- _ ] => (inversion H; clear H)
             | [ H : HaveData _ _ _ = HaveData _ _ _ |- _ ] => (inversion H; clear H)
             | [ H : _ |- _ ] => rewrite helper_1 in H
             | [ H : _ |- _ ] => rewrite N.add_sub in H
             | [ H : _ |- _ ] => rewrite N.leb_refl in H
             | [ H : appcontext[match ?E with _ => _ end] |- _ ] => revert H; case_eq E
             | [ |- appcontext[match ?E with _ => _ end] ] => case_eq E
             | [ H : ?x < ?y - ?z |- _ ] => unique simpl pose proof (proj2 (@N.lt_add_lt_sub_r _ _ _) H)
             | [ H : ?x < ?y, H' : ?y <= ?x |- _ ] => apply N.le_ngt in H'
             | [ H : ?a + ?b < ?y, H' : ?y <= ?b + ?a |- _ ] => apply N.le_ngt in H'; rewrite (N.add_comm a b) in H
             | [ H : ?x < ?y |- _ ] => unique simpl pose proof (H : _ = _)
             | [ H : ?x >= ?y |- _ ] => unique simpl pose proof (H : _ = _ -> False)
             | [ H : ?x - ?y < ?z |- _ ] => unique simpl pose proof (@N.lt_sub_lt_add_r _ _ _ H)
             | [ H : _ ?= _ = _ |- _ ] => unique simpl pose proof (N_compare_antisym_helper H : _ = Lt)
             | [ H : _ ?= _ = _ |- _ ] => unique simpl pose proof (N_compare_antisym_helper H : _ = Gt)
             | [ H : _ ?= _ = _ |- _ ] => unique simpl pose proof (N_compare_antisym_helper H : _ = Eq)
             | [ H : (_ <=? _) = false |- _ ] => unique simpl pose proof (proj1 (@N.leb_gt _ _) H)
             | [ H : (_ <=? _) = false |- _ ] => unique simpl pose proof (proj1 (@N.leb_nle _ _) H)
             | [ H : ?a < ?b |- _ ] => unique simpl pose proof (@N.lt_le_incl _ _ H)
             | [ H : (_ >? _) = true |- _ ] => unique simpl pose proof (proj1 (@N.ltb_lt _ _) H)
             | [ H : _ + 1 < _ |- _ ] => unique simpl pose proof (@N.le_lt_trans 0 _ _ (@N.le_0_l _) H)
           end.

  Lemma N2Nat1 x : N.of_nat x + 1 = N.of_nat (x + 1).
  Proof.
    rewrite Nat2N.inj_add; reflexivity.
  Qed.

  Hint Rewrite <- Nat2N.inj_sub Nat2N.inj_add Nat2N.inj_compare
       Compare_dec.nat_compare_gt Compare_dec.nat_compare_lt Compare_dec.nat_compare_eq : N2Nat.
  Hint Rewrite N.leb_compare N.ltb_compare : N2Nat.
  Hint Rewrite nat_compare_eq_iff : N2Nat.
  Hint Rewrite <- nat_compare_lt nat_compare_gt nat_compare_le nat_compare_ge : N2Nat.
  Hint Rewrite N2Nat1 : N2Nat.

  Lemma howManyMoreTicksNeeded_correct {T} (st : TickBoxState T) n
        (H : howManyMoreTicksNeeded st = WillWaitForMoreTicks n)
  : forall n', (n' < n -> fst (tickBoxLoopPreBody' st (inr (tbTick T n'))) = nil)
               /\ (n' >= n -> fst (tickBoxLoopPreBody' st (inr (tbTick T n'))) <> nil).
  Proof.
    intro n'.
    destruct st, (N.compare_spec n' n); t.
    (*repeat match goal with
               | _ => reflexivity
               | _ => congruence
               | _ => omega
               | _ => progress simpl in *
               | _ => progress subst
               | _ => intro
               | _ => progress unfold howManyMoreTicksNeeded, set_curData, readyToTransmit, readyToGetUpdate, ticksTooCoarseWaitingOnTicks, ticksTooCoarse in *
               | [ H : WillWaitForMoreTicks _ = WillWaitForMoreTicks _ |- _ ] => (inversion H; clear H)
               | [ H : WaitingOnData _ _ _ = WaitingOnData _ _ _ |- _ ] => (inversion H; clear H)
               | [ H : HaveData _ _ _ = HaveData _ _ _ |- _ ] => (inversion H; clear H)
               | [ H : appcontext[match ?E with _ => _ end] |- _ ] => revert H; case_eq E
               | [ |- appcontext[match ?E with _ => _ end] ] => case_eq E
               | [ |- _ /\ _ ] => split
               | [ x : N |- _ ] => generalize dependent x; intro x; rewrite <- (N2Nat.id x); generalize (N.to_nat x); clear x; intros x **
               | _ => hnf; progress repeat autorewrite with N2Nat
               | [ H : _ |- _ ] => hnf in H; progress repeat autorewrite with N2Nat in H
             end.*)
  Qed.
End howManyMoreTicksNeeded_correct.
