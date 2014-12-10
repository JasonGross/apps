Require Import Ascii FunctionApp List Program.Basics String System.
Require Import FunctionAppLemmas FunctionAppTactics.
Import ListNotations.
Open Scope string_scope.

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

  Definition uiLoopBody (uiLoop : list (string * string) -> process uiInput world) (pws : list (string * string))
  : uiInput -> action world * process uiInput world
    := (fun i =>
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

  CoFixpoint uiLoop (pws : list (string * string)) :=
    Step (uiLoopBody uiLoop pws).


  Definition ui := uiLoop nil.

End ui.


Section net.

  Inductive netInput :=
  | netReceived : option string -> netInput
  | netHttpError : httpResponse -> netInput
  | netEncrypted : string -> netInput.

  Context (world : Type).
  Context (httpPOST : string -> list (string * string) -> (httpResponse -> netInput) -> action world).
  Context (decrypt : string -> action world).

  Definition storageURI := "https://andersk.scripts.mit.edu/pwmgr/storage".
  Definition storageId := "foo".

  Definition storageGet id cb :=
    httpPOST
      (storageURI ++ "/get") [("id", id)]
      (fun r => match httpResponseStatus r with
                  | httpOk => cb (httpResponseBody r)
                  | _ => netHttpError r
                end).
  Definition storageSet id old new cb :=
    httpPOST
      (storageURI ++ "/set") [("id", id); ("old", old); ("new", new)]
      (fun r => match httpResponseStatus r with
                  | httpOk => cb None  (* compare-and-set succeeded *)
                  | httpPreconditionFailed => cb (Some (httpResponseBody r))  (* remote value differed *)
                  | _ => netHttpError r
                end).
  Definition storagePoll id old cb :=
    httpPOST
      (storageURI ++ "/poll") [("id", id); ("old", old)]
      (fun r => match httpResponseStatus r with
                  | httpOk => cb (httpResponseBody r)
                  | _ => netHttpError r
                end).

  CoFixpoint net :=
    Step (fun i =>
            match i with
              | netReceived (Some s) => (decrypt s, net)
              | netReceived None => (id, net)
              | netHttpError _ => (id, net)
              | netEncrypted s =>
                (storageSet storageId "" s netReceived,
                 net)
            end).

End net.


Definition getStep {input output} (p : process input output) :=
  match p with
    | Step f => f
  end.

Local Open Scope type_scope.

Section pwMgr.

  Inductive input :=
  | pwMgrConsoleIn : string -> input
  | pwMgrNetInput : netInput -> input
  | pwMgrEncrypt : string -> input
  | pwMgrDecrypt : string -> input.

  Context (world : Type).
  Context (sys : systemActions input world).

  Definition pwMgrLoopBody pwMgrLoop ui net : input -> action (stackWorld input world) * stackProcess input world :=
    fun i =>
      match i with
        | pwMgrEncrypt s =>
          (* TODO: crypto *)
          let (a, net') := getStep net (netEncrypted s) in (a, pwMgrLoop ui net')
        | pwMgrDecrypt s =>
          (* TODO: crypto *)
          let (a, ui') := getStep ui (uiDecrypted s) in (a, pwMgrLoop ui' net)
        | pwMgrConsoleIn s =>
          let (a, ui') := getStep ui (uiConsoleIn s) in
          (fun w => a (stackLift (consoleIn sys pwMgrConsoleIn) w), pwMgrLoop ui' net)
        | pwMgrNetInput i' =>
          let (a, net') := getStep net i' in (a, pwMgrLoop ui net')
      end.

  CoFixpoint pwMgrLoop ui net : stackProcess input world :=
    Step (pwMgrLoopBody pwMgrLoop ui net).

  Definition
    wrap_ui
    (ui :
       forall {world'},
         (string -> action world') ->
         (string -> action world') ->
         process uiInput world') :=
    ui
      (fun s => stackLift (consoleOut sys s))
      (fun s => stackPush (pwMgrEncrypt s)).

  Definition
    wrap_net
    (net :
       forall {world'},
         (string -> list (string * string) -> (httpResponse -> netInput) -> action world') ->
         (string -> action world') ->
         process netInput world') :=
    net
      (fun uri data cb => stackLift (httpPOST sys uri data (fun r => pwMgrNetInput (cb r))))
      (fun s => stackPush (pwMgrDecrypt s)).

  Definition
    mkPwMgrStack ui net :
    stackProcess input world :=
    pwMgrLoop (wrap_ui ui) (wrap_net net).

  Definition pwMgrStack := mkPwMgrStack ui net.


  Lemma pwMgrLoop_eta ui net
  : pwMgrLoop ui net = Step (pwMgrLoopBody pwMgrLoop ui net).
  Proof.
    rewrite stackProcess_eta at 1; reflexivity.
  Qed.

  CoFixpoint pwMgrGood' :
    forall pws, emptiesStackForever
      (Step (pwMgrLoopBody pwMgrLoop (wrap_ui (fun world uiConsoleOut uiEncrypt => uiLoop world uiConsoleOut uiEncrypt pws)) (wrap_net net))).
  Proof.
    intro; constructor.
    let tac := (idtac; 
                match goal with
                  | [ |- appcontext[match split ?a ?b with _ => _ end] ] => destruct (split a b)
                  | [ |- appcontext[match string_dec ?s0 ?s1 with _ => _ end] ] => destruct (string_dec s0 s1)
                  | [ |- appcontext[match ?l with nil => _ | _ => _ end] ] => destruct l
                  | [ |- appcontext[match find ?f ?ls with _ => _ end] ] => destruct (find f ls)
                  | [ |- appcontext[match ?x with (_, _) => _ end] ] => rewrite (@surjective_pairing _ _ x)
                  | [ |- appcontext[match ?a with (netReceived _) => _ | _ => _ end] ] => destruct a
                  | [ |- appcontext[match ?a with None => _ | _ => _ end] ] => destruct a
                  | _ => progress unfold storageSet in *
                end) in
    emptiesStackForever_t pwMgrGood' input (@pwMgrLoop_eta) (@pwMgrLoop) tac.

    - subst; discriminate.
    - subst.
      constructor.
      constructor.
      Grab Existential Variables.
      eauto.
  Qed.

  Theorem pwMgrGood pws :
    emptiesStackForever
      (mkPwMgrStack
         (fun world uiConsoleOut uiEncrypt => uiLoop world uiConsoleOut uiEncrypt pws)
         net).
  Proof.
    unfold mkPwMgrStack.
    rewrite pwMgrLoop_eta.
    eapply pwMgrGood'.
  Qed.

  Definition proc := (consoleIn sys pwMgrConsoleIn, runStackProcess pwMgrStack (pwMgrGood nil)).

End pwMgr.


Require Import ExtrOcamlBasic ExtrOcamlString.
Extraction "ExamplePwMgr" proc.
