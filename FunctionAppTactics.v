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
    | [ |- emptiesStack _ ?p ]
      => let p' := head p in
         constr_eq p' loop_pattern;
           rewrite loop_eta; simpl
    | _ => progress unfold id
    | _ => progress unfold compose
  (*| [ |- ?p = ?e ?x ] => let T := type of x in is_evar e; unify e (fun _ : T => p); reflexivity*)
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
    | [ |- exists _, emptiesStack _ _ /\ _ ] => econstructor; split;
                                                [ | solve [ eapply loopGood' ] ];
                                                clear loopGood'; solve [ emptiesStack_t loop_eta loop_pattern ] || fail 1 "Could not solve goal with emptiesStack_t"
    | [ |- emptiesStackForever ?p ]
      => let p' := head p in
         constr_eq p' loop_pattern;
           rewrite loop_eta; simpl
    | [ |- emptiesStackForever (Step _) ] => constructor
  end.

Ltac emptiesStackForever_t loopGood' inputT loop_eta loop_pattern tac :=
  repeat emptiesStackForever_t' loopGood' inputT loop_eta loop_pattern tac.
