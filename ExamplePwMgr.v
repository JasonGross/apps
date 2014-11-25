Require Import Ascii FunctionApp List Program.Basics String.
Import ListNotations.

Section ui.

  Inductive uiInput :=
  | uiConsoleIn : string -> uiInput
  | uiDecrypted : string -> uiInput.

  Context (world : Type).
  Context (consoleOut : string -> action world).
  Context (encrypt : string -> action world).

  Fixpoint split (sep : ascii) (s : string) : list string :=
    match s with
      | EmptyString => nil
      | String c s' =>
        if ascii_dec c sep then EmptyString :: split sep s'
        else match split sep s' with
               | nil => [String c EmptyString]
               | w :: ws => String c w :: ws
             end
    end.

  Definition newline := "010"%char.

  Definition dump (pws : list (string * string)) : string :=
    fold_right append ""%string
               (map (fun p => (fst p ++ " " ++ snd p ++ String newline "")%string) pws).

  Fixpoint load (s : string) : list (string * string) :=
    flat_map (fun l => match split " " l with
                         | account :: password :: nil => [(account, password)]
                         | _ => nil
                       end)
             (split newline s).

  Definition list_dec {A} (ls : list A) : { p | ls = fst p :: snd p } + { ls = nil }.
    destruct ls.
    - right; eauto.
    - left.
      exists (a, ls).
      eauto.
  Defined.

  CoFixpoint uiLoop (pws : list (string * string)) :=
    Step (fun i =>

            match i with
              | uiConsoleIn s =>
                match split " " s with
                  | comm :: ls =>
                    match string_dec comm "get", ls with
                      | left _, account :: nil =>
                        match
                          find (fun p => if string_dec account (fst p)
                                         then true else false) pws
                        with
                          | None =>
                            (consoleOut "account not found", uiLoop pws)
                          | Some (_, password) =>
                            (consoleOut password, uiLoop pws)
                        end
                      | _, _ =>
                        match string_dec comm "set", ls with
                          | left _,  account :: password :: nil =>
                            let pws' :=
                                (account, password)
                                  :: filter (fun p => if string_dec account (fst p)
                                                      then false else true) pws
                            in (encrypt (dump pws'), uiLoop pws')

                          | _, _ =>
                            (consoleOut "unrecognized command", uiLoop pws)
                        end
                    end
                  | _ => (consoleOut "unrecognized command", uiLoop pws)
                end
              | uiDecrypted s =>
                (id, uiLoop (load s))
            end).

  Definition ui := uiLoop nil.

End ui.


Section net.

  Inductive netInput :=
  | netReceived : string -> netInput
  | netEncrypted : string -> netInput.

  Context (world : Type).
  Context (send : string -> action world).
  Context (decrypt : string -> action world).

  CoFixpoint net :=
    Step (fun i =>
            match i with
              | netReceived s => (decrypt s, net)
              | netEncrypted s => (send s, net)
            end).

End net.


Definition getStep {input output} (p : process input output) :=
  match p with
    | Step f => f
  end.

Local Open Scope type_scope.

Section pwMgr.

  Context (world : Type).
  Context (consoleOut : string -> action world).
  Context (send : string -> action world).

  Inductive pwMgrMessage :=
  | pwMgrEncrypt : string -> pwMgrMessage
  | pwMgrDecrypt : string -> pwMgrMessage.

  Inductive pwMgrInput :=
  | pwMgrConsoleIn : string -> pwMgrInput
  | pwMgrReceived : string -> pwMgrInput.

  Definition pwMgrLoopBody pwMgrLoop ui net : @stackInput pwMgrMessage pwMgrInput -> action (stackWorld pwMgrMessage world) * stackProcess pwMgrMessage pwMgrInput world :=
    fun i =>
      match i with
        | inl (pwMgrEncrypt s) =>
          (* TODO: crypto *)
          let (a, net') := getStep net (netEncrypted s) in (a, pwMgrLoop ui net')
        | inl (pwMgrDecrypt s) =>
          (* TODO: crypto *)
          let (a, ui') := getStep ui (uiDecrypted s) in (a, pwMgrLoop ui' net)
        | inr (pwMgrConsoleIn s) =>
          let (a, ui') := getStep ui (uiConsoleIn s) in (a, pwMgrLoop ui' net)
        | inr (pwMgrReceived s) =>
          let (a, net') := getStep net (netReceived s) in (a, pwMgrLoop ui net')
      end.

  CoFixpoint pwMgrLoop ui net : stackProcess pwMgrMessage pwMgrInput world :=
    Step (pwMgrLoopBody pwMgrLoop ui net).

  Definition 
    wrap_ui
    (ui :
       forall {world'},
         (string -> action world') ->
         (string -> action world') ->
         process uiInput world') :=
    ui
      (fun s => stackLift (consoleOut s))
      (fun s => stackPush (pwMgrEncrypt s)).

  Definition
    wrap_net
    (net :
       forall {world'},
         (string -> action world') ->
         (string -> action world') ->
         process netInput world') :=
    net
      (fun s => stackLift (send s))
      (fun s => stackPush (pwMgrDecrypt s)).

  Definition
    mkPwMgrStack ui net :
    stackProcess pwMgrMessage pwMgrInput world :=
    pwMgrLoop (wrap_ui ui) (wrap_net net).

  Definition pwMgrStack := mkPwMgrStack ui net.

  Require Import FunctionAppLemmas.

  Lemma pwMgrLoop_eta ui net 
  : pwMgrLoop ui net = Step (pwMgrLoopBody pwMgrLoop ui net).
  Proof.
    rewrite stackProcess_eta at 1; reflexivity.
  Qed.

  CoFixpoint pwMgrGood' :
    forall pws, emptiesStackForever
      (pwMgrLoop (wrap_ui (fun world uiConsoleOut uiEncrypt => uiLoop world uiConsoleOut uiEncrypt pws)) (wrap_net net)).
  Proof.
    intros.
    rewrite pwMgrLoop_eta.
    econstructor.
    intros.
    unfold stackTransition; simpl.
    destruct i; simpl.
    destruct (split " " s); simpl.
    eexists.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    destruct (string_dec s0 "get"); simpl.
    destruct l; simpl.
    destruct (string_dec s0 "set"); simpl.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    destruct l; simpl.
    destruct (find (fun p => if string_dec s1 (fst p) then true else false) pws); simpl.
    destruct p; simpl.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    destruct (string_dec s0 "set"); simpl.
    destruct l; simpl.
    rewrite pwMgrLoop_eta.
    econstructor.
    econstructor.
    econstructor.
    unfold stackTransition; simpl.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    destruct (string_dec s0 "set"); simpl.
    destruct l; simpl.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    destruct l; simpl.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    destruct l; simpl.
    rewrite pwMgrLoop_eta.
    econstructor.
    econstructor.
    econstructor.
    unfold stackTransition; simpl.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
    rewrite pwMgrLoop_eta.
    econstructor.
    econstructor.
    econstructor.
    unfold stackTransition; simpl.
    econstructor.
    econstructor.
    eapply pwMgrGood'.
    Guarded.
  Qed.

  Theorem pwMgrGood pws :
    emptiesStackForever
      (mkPwMgrStack
         (fun world uiConsoleOut uiEncrypt => uiLoop world uiConsoleOut uiEncrypt pws)
         net).
  Proof.
    eapply pwMgrGood'.
  Qed.

  Definition pwMgr := runStackProcess pwMgrStack (pwMgrGood nil).

End pwMgr.


Require Import ExtrOcamlBasic ExtrOcamlString.
Extraction "ExamplePwMgr" pwMgr.
