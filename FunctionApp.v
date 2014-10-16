Section process.
  Context {input : Type}.
  Context {world : Type}.

  CoInductive process :=
  | Step : (input -> (world -> world) * process) -> process.

  Definition action := world -> world.

  Definition runStep wp i :=
    match wp with
      | (w, Step pf) => let (a, p') := pf i in (a w, p')
    end.
End process.

Arguments process : clear implicits.
Arguments action : clear implicits.


Section stackProcess.

  Context {message : Type}.
  Context {input : Type}.
  Context {world : Type}.

  Definition stackWorld := (list message * action world)%type.
  Definition stackProcess := process (message + input) stackWorld.

  Definition stackPush (m : message) : action stackWorld :=
    fun sw => let (ms, a) := sw in ((m :: ms)%list, a).
  Definition stackLift (a : action world) : action stackWorld :=
    fun sw => let (ms, a') := sw in (ms, fun w => a (a' w)).

  Inductive emptiesStack :
    stackWorld * stackProcess -> Prop :=
  | stackEmpty p :
      emptiesStack (nil, @id world, p)
  | popsStack m ms a p :
      emptiesStack (runStep (ms, a, p) (inl m)) ->
      emptiesStack ((m :: ms)%list, a, p).

  Fixpoint stepStackProcess swp (h : emptiesStack swp) : action world * stackProcess.
  destruct swp as [[[ | m ms] a] p].
  { exact (a, p). }
  {
    refine (stepStackProcess (runStep (ms, a, p) (inl m)) _).
    inversion h; trivial.
  }
  Defined.

  CoInductive emptiesStackForever : stackProcess -> Prop :=
  | emptiesStackStep p h :
      (forall (i : input),
         emptiesStackForever (snd (stepStackProcess
                                     (runStep (nil, @id world, p) (inr i)) (h i)))) ->
      emptiesStackForever p.

  CoFixpoint runStackProcess (p : stackProcess) (h : emptiesStackForever p) : process input world.
  refine
    (Step (fun i =>
             let ap' :=
                 stepStackProcess
                   (runStep (nil, @id world, p) (inr i))
                   match h with
                     | emptiesStackStep _ h1 _ => h1 i
                   end in
             (fst ap', runStackProcess (snd ap') _))).
  destruct h; eauto.
  Defined.

End stackProcess.

Arguments stackWorld : clear implicits.
Arguments stackProcess : clear implicits.
