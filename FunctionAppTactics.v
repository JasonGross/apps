Require Import Coq.Program.Program.
Require Import FunctionApp FunctionAppLemmas.
Require Import Common.

Local Open Scope type_scope.

Ltac emptiesStack_t' loop_eta loop_pattern :=
  idtac;
  match goal with
    | _ => intro
    | [ |- { p : _ & emptiesStack (stackTransition _ _) p * _ } ] => unfold stackTransition; simpl
    | [ |- { p : _ & emptiesStack (stackPush _ _, Step _) p * _ } ] => apply emptiesStackPush_sigT
    | [ |- { p : _ & emptiesStack (stackLift _ _, _) p * _ } ] => apply emptiesStackLift_sigT
    | [ |- { p : _ & emptiesStack (stackDone, _) p * _ } ] => apply emptiesStackDone_sigT
    | [ |- { q : _ & emptiesStack (_, ?p) q * _ } ]
      => let p' := head p in
         constr_eq p' loop_pattern;
           rewrite loop_eta; simpl
    | _ => progress unfold id
    | _ => progress unfold compose
  (*| [ |- ?p = ?e ?x ] => let T := type of x in is_evar e; unify e (fun _ : T => p); reflexivity*)
  end.

Ltac emptiesStack_t loop_eta loop_pattern := repeat emptiesStack_t' loop_eta loop_pattern.

Ltac emptiesStackForever_t' loopGood' inputT loop_eta loop_pattern :=
  idtac;
  match goal with
    | _ => progress simpl in *
    | _ => intro
    | [ |- _ /\ _ ] => split
    | [ |- _ * _ ] => split
    | [ H : inputT |- _ ] => destruct H
    | [ |- { _ : _ & emptiesStack _ _ * _ } ] => clear loopGood'; emptiesStack_t loop_eta loop_pattern
    | [ |- emptiesStackForever (Step _) ] => apply loopGood'
    | [ |- emptiesStackForever ?p ]
      => let p' := head p in
         constr_eq p' loop_pattern;
           rewrite loop_eta; simpl
  end.

Ltac emptiesStackForever_t loopGood' inputT loop_eta loop_pattern :=
  repeat emptiesStackForever_t' loopGood' inputT loop_eta loop_pattern.
