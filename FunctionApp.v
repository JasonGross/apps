Section process.
  Context {input : Type}.
  Context {world : Type}.

  Definition action := world -> world.

  CoInductive process :=
  | Step : (input -> action * process) -> process.

  Definition step := input -> action * process.
End process.

Arguments action : clear implicits.
Arguments process : clear implicits.
Arguments step : clear implicits.


Section stackProcess.

  Context {message : Type}.
  Context {input : Type}.
  Context {world : Type}.

  Inductive stackWorld :=
  | stackDone : stackWorld
  | stackPush : message -> action stackWorld
  | stackLift : action world -> action stackWorld.

  Definition stackInput := (message + input)%type.
  Definition stackProcess := process stackInput stackWorld.
  Definition stackStep := step stackInput stackWorld.

  Definition stackTransition (m : stackInput) (pf : stackStep) :=
    (fst (pf m) stackDone, snd (pf m)).

  Inductive emptiesStack : stackWorld * stackProcess -> stackProcess -> Prop :=
  | emptiesStackDone p : emptiesStack (stackDone, p) p
  | emptiesStackPush m sw pf p2 p3 :
      emptiesStack (stackTransition (inl m) pf) p2 ->
      emptiesStack (sw, p2) p3 ->
      emptiesStack (stackPush m sw, Step pf) p3
  | emptiesStackLift a sw p p2 :
      emptiesStack (sw, p) p2 ->
      emptiesStack (stackLift a sw, p) p2.

  CoInductive emptiesStackForever : stackProcess -> Prop :=
  | emptiesStackStep pf p' :
      (forall (i : input),
         emptiesStack (stackTransition (inr i) pf) (p' i) /\
         emptiesStackForever (p' i)) ->
      emptiesStackForever (Step pf).

  Inductive stepStackProcessTerminates : stackWorld * stackProcess -> Prop :=
  | stepStackProcessDone p : stepStackProcessTerminates (stackDone, p)
  | stepStackProcessPush m sw pf p2 :
      stepStackProcessTerminates (stackTransition (inl m) pf) ->
      emptiesStack (stackTransition (inl m) pf) p2 ->
      stepStackProcessTerminates (sw, p2) ->
      stepStackProcessTerminates (stackPush m sw, Step pf)
  | stepStackProcessLift a sw p p2 :
      stepStackProcessTerminates (sw, p) ->
      emptiesStack (sw, p) p2 ->
      stepStackProcessTerminates (stackLift a sw, p).

  Theorem mkStepStackProcessTerminates swp p' (e : emptiesStack swp p') : stepStackProcessTerminates swp.
    induction e; econstructor; eauto.
  Qed.

  Fixpoint stepStackProcess swp (h : stepStackProcessTerminates swp) :
    action world * sig (unique (emptiesStack swp)).
  destruct swp as [[| m sw' | a sw'] p].
  {
    split.
    { exact (@id world). }
    {
      exists p.
      split.
      { constructor. }
      {
        inversion 1.
        reflexivity.
      }
    }
  }
  {
    destruct p as [pf].
    pose (sap1 := pf (inl m)).
    pose (sw := fst sap1 stackDone).
    assert (stepStackProcessTerminates (sw, snd sap1)) as e1 by (inversion h; assumption).
    destruct (stepStackProcess (sw, snd sap1) e1) as [a2 [p2 [e2 u2]]].
    assert (stepStackProcessTerminates (sw', p2)) as e3.
    {
      inversion h as [| ? ? ? p' |].
      rewrite (u2 p'); assumption.
    }
    destruct (stepStackProcess (sw', p2) e3) as [a3 [p3 [e4 u4]]].
    split.
    { exact (fun w => a2 (a3 w)). }
    {
      exists p3.
      split.
      { econstructor; eassumption. }
      {
        intros p3' e5.
        apply u4.
        inversion e5 as [| ? ? ? p' |].
        rewrite (u2 p'); assumption.
      }
    }
  }
  {
    assert (stepStackProcessTerminates (sw', p)) as e1 by (inversion h; assumption).
    destruct (stepStackProcess (sw', p) e1) as [a2 [p2 [e2 u2]]].
    split.
    { exact (fun w => a (a2 w)). }
    {
      exists p2.
      split.
      { constructor. assumption. }
      {
        intros p2' h1.
        apply u2.
        inversion h1.
        assumption.
      }
    }
  }
  Defined.

  CoFixpoint runStackProcess (p : stackProcess) (h : emptiesStackForever p) : process input world.
  constructor.
  intro i.
  destruct p as [pf].
  pose (sap1 := pf (inr i)).
  pose (sw := fst sap1 stackDone).
  assert (stepStackProcessTerminates (sw, snd sap1)) as e1.
  {
    inversion h as [? ? h1].
    destruct (h1 i).
    eapply mkStepStackProcessTerminates.
    eassumption.
  }
  destruct (stepStackProcess (sw, snd sap1) e1) as [a2 [p2 [e2 u2]]].
  split.
  { exact a2. }
  {
    apply (runStackProcess p2).
    inversion h as [? p' h1].
    destruct (h1 i).
    rewrite (u2 (p' i)); assumption.
  }
  Defined.

End stackProcess.

Arguments stackWorld : clear implicits.
Arguments stackProcess : clear implicits.
