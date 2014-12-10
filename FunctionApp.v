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

  Context {input : Type}.
  Context {world : Type}.

  Inductive stackWorld :=
  | stackDone : stackWorld
  | stackPush : input -> action stackWorld
  | stackLift : action world -> action stackWorld.

  Definition stackProcess := process input stackWorld.
  Definition stackStep := step input stackWorld.

  Definition stackTransition (m : input) (pf : stackStep) :=
    (fst (pf m) stackDone, snd (pf m)).

  Inductive emptiesStack : stackWorld * stackProcess -> stackProcess -> Prop :=
  | emptiesStackDone p : emptiesStack (stackDone, p) p
  | emptiesStackPush m sw pf p2 p3 :
      emptiesStack (stackTransition m pf) p2 ->
      emptiesStack (sw, p2) p3 ->
      emptiesStack (stackPush m sw, Step pf) p3
  | emptiesStackLift a sw p p2 :
      emptiesStack (sw, p) p2 ->
      emptiesStack (stackLift a sw, p) p2.

  CoInductive emptiesStackForever : stackProcess -> Prop :=
  | emptiesStackStep pf:
      (forall (i : input), exists p',
         emptiesStack (stackTransition i pf) p' /\
         emptiesStackForever p') ->
      emptiesStackForever (Step pf).

  Inductive stepStackProcessTerminates : stackWorld * stackProcess -> Prop :=
  | stepStackProcessDone p : stepStackProcessTerminates (stackDone, p)
  | stepStackProcessPush m sw pf p2 :
      stepStackProcessTerminates (stackTransition m pf) ->
      emptiesStack (stackTransition m pf) p2 ->
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
    pose (sap1 := pf m).
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
  Proof.
    refine (Step (fun i =>
                    match p as p return emptiesStackForever p -> _ with
                      | Step pf => fun h' => let sap1 := pf i in
                                             let sw := fst sap1 stackDone in
                                             let stepped := stepStackProcess (sw, snd sap1) _ in
                                             (fst stepped, runStackProcess (proj1_sig (snd stepped)) _)
                    end h));
    clear runStackProcess p h.
    {
      inversion h' as [? h1]; subst.
      destruct (h1 i) as [? [? ?]]; clear h1.
      eapply mkStepStackProcessTerminates.
      eassumption.
    }
    {
      inversion h' as [? h1]; subst.
      destruct (h1 i) as [? [? ?]].
      erewrite (proj2 (proj2_sig (snd stepped))); eassumption.
    }
  Defined.

End stackProcess.

Arguments stackWorld : clear implicits.
Arguments stackProcess : clear implicits.
