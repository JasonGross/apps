Section process.
  Context {input : Type}.
  Context {world : Type}.

  CoInductive process :=
  | Step : (input -> (world -> world) * process) -> process.

  Definition action := world -> world.
  Definition step := input -> action * process.

  Definition runStep wp i :=
    match wp with
      | (w, Step pf) => let (a, p') := pf i in (a w, p')
    end.
End process.

Arguments process : clear implicits.
Arguments step : clear implicits.
Arguments action : clear implicits.


Section stackProcess.

  Context {message : Type}.
  Context {input : Type}.
  Context {world : Type}.

  Definition stackWorld := (list message * action world)%type.
  Definition stackInput := (message + input)%type.
  Definition stackProcess := process stackInput stackWorld.
  Definition stackStep := step stackInput stackWorld.

  Definition stackPush (m : message) : action stackWorld :=
    fun sw => let (ms, a) := sw in ((m :: ms)%list, a).
  Definition stackLift (a : action world) : action stackWorld :=
    fun sw => let (ms, a') := sw in (ms, fun w => a (a' w)).

  Definition stackTransition (m : stackInput) (pf : stackStep) :=
    (fst (fst (pf m) (nil, @id world)), snd (pf m)).

  Inductive emptiesStack : list message * stackProcess -> stackProcess -> Prop :=
  | stackEmpty p : emptiesStack (nil, p) p
  | popsStack (m : message) (ms : list message) (pf : stackStep) (p2 p3 : stackProcess) :
      emptiesStack (stackTransition (inl m) pf) p2 ->
      emptiesStack (ms, p2) p3 ->
      emptiesStack ((m :: ms)%list, Step pf) p3.

  CoInductive emptiesStackForever : stackProcess -> Prop :=
  | emptiesStackStep pf p' :
      (forall (i : input),
         emptiesStack (stackTransition (inr i) pf) (p' i) /\
         emptiesStackForever (p' i)) ->
      emptiesStackForever (Step pf).

  Inductive stepStackProcessTerminates : list message * stackProcess -> Prop :=
  | stepStackProcessDone p : stepStackProcessTerminates (nil, p)
  | stepStackProcessStep m ms pf p2 :
      stepStackProcessTerminates (stackTransition (inl m) pf) ->
      emptiesStack (stackTransition (inl m) pf) p2 ->
      stepStackProcessTerminates (ms, p2) ->
      stepStackProcessTerminates ((m :: ms)%list, Step pf).

  Fixpoint mkStepStackProcessTerminates mp p' (e : emptiesStack mp p') : stepStackProcessTerminates mp.
  destruct e; econstructor; eauto.
  Defined.

  Fixpoint stepStackProcess mp (h : stepStackProcessTerminates mp) :
    action world * sig (unique (emptiesStack mp)).
  destruct mp as [[| m ms] p].
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
    pose (sw := fst sap1 (nil, @id world)).
    assert (stepStackProcessTerminates (fst sw, snd sap1)) as e1 by (inversion h; assumption).
    destruct (stepStackProcess (fst sw, snd sap1) e1) as [a2 [p2 [e2 u2]]].
    assert (stepStackProcessTerminates (ms, p2)) as e3.
    {
      inversion h as [| ? ? ? p'].
      rewrite (u2 p'); assumption.
    }
    destruct (stepStackProcess (ms, p2) e3) as [a3 [p3 [e4 u4]]].
    split.
    { exact (fun w => a3 (a2 (snd sw w))). }
    {
      exists p3.
      split.
      { econstructor; eassumption. }
      {
        intros p3' e5.
        apply u4.
        inversion e5 as [| ? ? ? p'].
        rewrite (u2 p'); assumption.
      }
    }
  }
  Defined.

  CoFixpoint runStackProcess (p : stackProcess) (h : emptiesStackForever p) : process input world.
  constructor.
  intro i.
  destruct p as [pf].
  pose (sap1 := pf (inr i)).
  pose (sw := fst sap1 (nil, @id world)).
  assert (stepStackProcessTerminates (fst sw, snd sap1)) as e1.
  {
    inversion h as [? ? h1].
    destruct (h1 i).
    eapply mkStepStackProcessTerminates.
    eassumption.
  }
  destruct (stepStackProcess (fst sw, snd sap1) e1) as [a2 [p2 [e2 u2]]].
  split.
  { exact (fun w => a2 (snd sw w)). }
  {
    apply (runStackProcess p2).
    inversion h as [? ? h1].
    destruct (h1 i).
    rewrite (u2 (p' i)); assumption.
  }
  Defined.

End stackProcess.

Arguments stackWorld : clear implicits.
Arguments stackProcess : clear implicits.
