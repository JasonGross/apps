Require Import FunctionApp.

(** We apply AC_∞, the type-theoretic axiom of choice, so that
          we don't need to do higher order unification later. *)
Lemma emptiesStackStep' message input world pf
      (H : forall i : input,
             { p' : stackProcess message input world
             | emptiesStack (stackTransition (inr i) pf) p' /\
               emptiesStackForever p' })
: @emptiesStackForever message input world (Step pf).
Proof.
  econstructor.
  intro i.
  instantiate (1 := fun i' => projT1 (H i')).
  exact (projT2 (H _)).
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
