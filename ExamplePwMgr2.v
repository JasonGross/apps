Require Import Ascii FunctionApp List Program.Basics String.
Import ListNotations.

Section ui.

  Inductive uiInput :=
  | uiConsoleIn : string -> uiInput
  | uiDecrypted : string -> uiInput.

  Inductive uiOutput :=
  | uiConsoleOut : string -> uiOutput
  | uiEncrypt : string -> uiOutput
  | uiNoop : uiOutput.

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

  Definition uiState := list (string * string).

  Open Scope string_scope.

  Definition ui (pws : uiState) (i : uiInput) : (uiOutput * uiState) :=
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
                    (uiConsoleOut "account not found", pws)
                  | Some (_, password) =>
                    (uiConsoleOut password, pws)
                end
              | _, _ =>
                match string_dec comm "set", ls with
                  | left _,  account :: password :: nil =>
                    let pws' :=
                        (account, password)
                          :: filter (fun p => if string_dec account (fst p)
                                              then false else true) pws
                    in (uiEncrypt (dump pws'), pws')

                  | _, _ =>
                    (uiConsoleOut "unrecognized command", pws)
                end
            end
          | _ => (uiConsoleOut "unrecognized command", pws)
        end
      | uiDecrypted s =>
        (uiNoop, load s)
    end.

  Definition uiStateInit : uiState := nil.

End ui.


Section net.

  Inductive netInput :=
  | netReceived : string -> netInput
  | netEncrypted : string -> netInput.

  Inductive netOutput :=
  | netDecrypt : string -> netOutput
  | netSend : string -> netOutput.

  Definition net (i : netInput) :=
    match i with
      | netReceived s => netDecrypt s
      | netEncrypted s => netSend s
    end.

End net.


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

  Definition uiOutputDec (out : uiOutput) : {s | out = uiConsoleOut s} + {s | out = uiEncrypt s} + {out = uiNoop}.
    destruct out.
    - left; left; eexists; eauto.
    - left; right; eexists; eauto.
    - right; eauto.
  Defined.

  Definition netOutputDec (out : netOutput) : {s | out = netDecrypt s} + {s | out = netSend s}.
    destruct out.
    - left; eexists; eauto.
    - right; eexists; eauto.
  Defined.

  Ltac unfold_all :=
    repeat match goal with
             | H := _ |- _ => unfold H in *; clear H
           end.

  Lemma ui_ConsoleIn_not_Noop st s : fst (ui st (uiConsoleIn s)) <> uiNoop.
  Proof.
    intros H.
    unfold ui in *.
    destruct (split " ") as [ | comm ls].
    { simpl in *; discriminate. }
    { 
      destruct (string_dec comm "get").
      {
        destruct ls.
        { destruct (string_dec comm "set"); simpl in *; discriminate. }
        destruct ls.
        { destruct (find (fun p => if string_dec s0 (fst p) then true else false) st); try destruct p; simpl in *; discriminate. }
        destruct (string_dec comm "set").
        { destruct ls; simpl in *; discriminate. }
        simpl; discriminate.
      }
      {
        destruct (string_dec comm "set").
        {
          destruct ls.
          { simpl in *; discriminate. }
          destruct ls.
          { simpl in *; discriminate. }
          { destruct ls; simpl in *; discriminate. }
        }
        { simpl in *; discriminate. }
      }          
    }
  Qed.

  CoFixpoint pwMgrLoop (ui_st : uiState) : process pwMgrInput world.
  refine
    (Step (fun i =>
             match i with
               | pwMgrConsoleIn s =>
                 let r := ui ui_st (uiConsoleIn s) in 
                 let a := fst r in
                 let ui_st' := snd r in
                 match uiOutputDec a with
                   | inleft (inl (exist s _)) => (consoleOut s, pwMgrLoop ui_st')
                   | inleft (inr (exist s _)) =>
                     (* TODO: crypto *)
                     let a := net (netEncrypted s) in
                     match netOutputDec a with
                       | inr (exist s _) => (send s, pwMgrLoop ui_st')
                       | _ => _
                     end
                   | _ => _
                 end
               | pwMgrReceived s =>
                 let a := net (netReceived s) in
                 match netOutputDec a with 
                   | inl (exist s _) =>
                     (* TODO: crypto *)
                     let (_, ui_st') := ui ui_st (uiDecrypted s) in (id, pwMgrLoop ui_st') 
                   | _ => _
                 end
             end)).
  - unfold_all.
    simpl in s3.
    destruct s3; discriminate.
  - unfold_all.
    simpl.
    contradict e; eapply ui_ConsoleIn_not_Noop.
  - unfold_all.
    simpl in s0.
    destruct s0; discriminate.
  Defined.

  Definition pwMgr := pwMgrLoop uiStateInit.

End pwMgr.


Require Import ExtrOcamlBasic ExtrOcamlString.
Extraction "ExamplePwMgr" pwMgr.
