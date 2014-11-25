Require Import Coq.Program.Program.
Require Import FunctionApp FunctionAppLemmas.
Require Import Common.

Local Open Scope type_scope.

Ltac emptiesStack_t' loop_eta loop_pattern :=
  idtac;
  match goal with
    | _ => intro
    | [ |- emptiesStack (stackTransition _ _) ?e ] => unfold stackTransition; simpl
    | [ |- emptiesStack (stackPush _ _, Step _) ?e ] => eapply emptiesStackPush
    | [ |- emptiesStack (stackLift _ _, _) ?e ] => apply emptiesStackLift
    | [ |- emptiesStack (stackDone, _) ?e ] => apply emptiesStackDone
    | [ |- emptiesStack (_, ?p) ?e ]
      => let p' := head p in
         constr_eq p' loop_pattern;
           rewrite loop_eta; simpl
    | _ => progress unfold id
    | _ => progress unfold compose
  end.

Ltac emptiesStack_t loop_eta loop_pattern := repeat emptiesStack_t' loop_eta loop_pattern.

Ltac emptiesStackForever_t' loopGood' inputT loop_eta loop_pattern tac :=
  idtac;
  match goal with
    | _ => progress simpl in *
    | _ => intro
    | [ |- _ /\ _ ] => split
    | [ |- _ * _ ] => split
    | [ H : inputT |- _ ] => destruct H
    | _ => progress unfold stackTransition, compose
    | _ => progress tac
    | [ |- exists p : _, emptiesStack _ p /\ _ ]
      => (eexists; split; [ clear loopGood' | try solve [ apply loopGood' ] ];
          emptiesStack_t loop_eta loop_pattern)
    | [ |- emptiesStackForever ?p ]
      => let p' := head p in
         constr_eq p' loop_pattern;
           rewrite loop_eta; simpl
    | [ |- emptiesStackForever (Step _) ] => apply loopGood'
  end.

Ltac emptiesStackForever_t loopGood' inputT loop_eta loop_pattern tac :=
  repeat emptiesStackForever_t' loopGood' inputT loop_eta loop_pattern tac.
