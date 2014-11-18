Require Import FunctionApp.

Ltac emptiesStack_t' loop_eta loop_pattern :=
  idtac;
  match goal with
    | [ |- emptiesStack (stackTransition _ _) _ ] => unfold stackTransition; simpl
    | [ |- emptiesStack (stackPush _ _, _) _ ] => econstructor
    | [ |- emptiesStack (stackLift _ _, _) _ ] => econstructor
    | [ |- emptiesStack (stackDone, _) _ ] => constructor
    | [ |- emptiesStack (_, ?p) _ ]
      => let p' := head p in
         constr_eq p' loop_pattern;
           rewrite loop_eta; simpl
    | [ |- emptiesStack (stackDone, ?p) ?q ] => apply emptiesStackDone'
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
    | [ H : inputT |- _ ] => destruct H
    | [ |- emptiesStack _ _ ] => clear loopGood'; emptiesStack_t loop_eta loop_pattern
    | [ |- sig _ ] => eexists
    | [ |- emptiesStackForever (Step _) ] => apply loopGood'
    | [ |- emptiesStackForever ?p ]
      => let p' := head p in
         constr_eq p' loop_pattern;
           rewrite loop_eta; simpl
  end.

Ltac emptiesStackForever_t loopGood' inputT loop_eta loop_pattern :=
  repeat emptiesStackForever_t' loopGood' inputT loop_eta loop_pattern.
