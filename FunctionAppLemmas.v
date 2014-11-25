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
  exists (projT1 (H i)).
  split; apply (projT2 (H _)).
Defined.

Definition stackProcess_eta message input world (p : stackProcess message input world)
: p = match p with
        | Step f => Step f
      end.
Proof.
  destruct p; reflexivity.
Defined.

Definition process_eta input world (p : process input world)
: p = match p with
        | Step f => Step f
      end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma emptiesStackDone' message input world p q (H : p = q) : @emptiesStack message input world (stackDone, p) q.
Proof.
  subst.
  constructor.
Defined.

Lemma emptiesStackPush_sigT {message input world} (m : message) (sw : stackWorld message world)
      (pf : stackStep) P
: { p2 : stackProcess message input world & emptiesStack (stackTransition (inl m) pf) p2 * { p3 : _ & emptiesStack (sw, p2) p3 * P p3 } }
  -> { p3 : _ & emptiesStack (stackPush m sw, Step pf) p3 * P p3 }.
Proof.
  intro H.
  eexists.
  split; [ eapply emptiesStackPush | ];
  first [ apply (fst (projT2 H))
        | apply (fst (projT2 (snd (projT2 H))))
        | apply (snd (projT2 (snd (projT2 H)))) ].
Defined.

Lemma emptiesStackLift_sigT {message input world} (a : action world) (sw : stackWorld message world)
      (p : stackProcess message input world) P
: { p2 : _ & emptiesStack (sw, p) p2 * P p2 }
  -> { p2 : _ & emptiesStack (stackLift a sw, p) p2 * P p2 }.
Proof.
  intro H.
  eexists.
  split; [ eapply emptiesStackLift | ];
  first [ apply (fst (projT2 H))
        | apply (snd (projT2 H)) ].
Defined.

Lemma emptiesStackDone_sigT {message input world} p (P : stackProcess message input world -> Type)
: P p -> { p' : _ & emptiesStack (stackDone, p) p' * P p' }.
Proof.
  intro H.
  eexists.
  split; [ eapply emptiesStackDone | ]; eassumption.
Defined.

Lemma emptiesStackPush_ex {message input world} (m : message) (sw : stackWorld message world)
      (pf : stackStep) P
: (exists p2 : stackProcess message input world,
     emptiesStack (stackTransition (inl m) pf) p2
     /\ exists p3 : _, emptiesStack (sw, p2) p3 /\ P p3)
  -> exists p3 : _, emptiesStack (stackPush m sw, Step pf) p3 /\ P p3.
Proof.
  intros [? [? [? [? ?]]]].
  eexists.
  split; [ eapply emptiesStackPush | ];
  eassumption.
Defined.

Lemma emptiesStackLift_ex {message input world} (a : action world) (sw : stackWorld message world)
      (p : stackProcess message input world) P
: (exists p2 : _, emptiesStack (sw, p) p2 /\ P p2)
  -> exists p2 : _, emptiesStack (stackLift a sw, p) p2 /\ P p2.
Proof.
  intros [? [? ?]].
  eexists.
  split; [ eapply emptiesStackLift | ];
  eassumption.
Defined.

Lemma emptiesStackDone_ex {message input world} p (P : stackProcess message input world -> Prop)
: P p -> exists p' : _, emptiesStack (stackDone, p) p' /\ P p'.
Proof.
  intro H.
  eexists.
  split; [ eapply emptiesStackDone | ]; eassumption.
Defined.
