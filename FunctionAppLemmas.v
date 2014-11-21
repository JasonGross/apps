Require Import FunctionApp.

Local Open Scope type_scope.

(** We apply AC_∞, the type-theoretic axiom of choice, so that
          we don't need to do higher order unification later. *)
Lemma emptiesStackStep' message input world pf
      (H : forall i : input,
             { p' : stackProcess message input world
             & emptiesStack (stackTransition (inr i) pf) p' *
               emptiesStackForever p' })
: @emptiesStackForever message input world (Step pf).
Proof.
  econstructor.
  intro i.
  instantiate (1 := fun i' => projT1 (H i')).
  split; apply (projT2 (H _)).
Defined.

Definition stackProcess_eta message input world (p : stackProcess message input world)
: p = match p with
        | Step f => Step f
      end.
Proof.
  destruct p; reflexivity.
Qed.

Definition process_eta input world (p : process input world)
: p = match p with
        | Step f => Step f
      end.
Proof.
  destruct p; reflexivity.
Qed.

Lemma emptiesStackDone' message input world p q (H : p = q) : @emptiesStack message input world (stackDone, p) q.
Proof.
  subst.
  constructor.
Qed.

Lemma emptiesStackPush_sigT {message input world} (m : message) (sw : stackWorld message world)
      (pf : stackStep) P
: { p2 : stackProcess message input world & emptiesStack (stackTransition (inl m) pf) p2 * { p3 : _ & emptiesStack (sw, p2) p3 * P p3 } }
  -> { p3 : _ & emptiesStack (stackPush m sw, Step pf) p3 * P p3 }.
Proof.
  intros [? [? [? [? ?]]]].
  eexists.
  split; try eapply emptiesStackPush; eassumption.
Qed.

Lemma emptiesStackLift_sigT {message input world} (a : action world) (sw : stackWorld message world)
      (p : stackProcess message input world) P
: { p2 : _ & emptiesStack (sw, p) p2 * P p2 }
  -> { p2 : _ & emptiesStack (stackLift a sw, p) p2 * P p2 }.
Proof.
  intros [? [? ?]].
  eexists.
  split; try eapply emptiesStackLift; eassumption.
Qed.

Lemma emptiesStackDone_sigT {message input world} p (P : stackProcess message input world -> Type)
: P p -> { p' : _ & emptiesStack (stackDone, p) p' * P p' }.
Proof.
  intro H.
  eexists.
  split; try eapply emptiesStackDone; eassumption.
Qed.
