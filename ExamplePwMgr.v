Require Import Ascii FunctionApp List String.
Import ListNotations.

Inductive uiInput :=
  | uiConsoleIn : string -> uiInput
  | uiDecrypted : string -> uiInput.

Inductive uiOutput :=
  | uiConsoleOut : string -> uiOutput
  | uiEncrypt : string -> uiOutput.

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

CoFixpoint uiLoop (pws : list (string * string)) :=
  Step (fun i =>
          match i with

            | uiConsoleIn s =>
              match split " " s with

                | "get"%string :: account :: nil =>
                  match
                    find (fun p => if string_dec account (fst p)
                                   then true else false) pws
                  with
                    | None =>
                      ([uiConsoleOut "account not found"], uiLoop pws)
                    | Some (_, password) =>
                      ([uiConsoleOut password], uiLoop pws)
                  end

                | "set"%string :: account :: password :: nil =>
                  let pws' :=
                      (account, password)
                        :: filter (fun p => if string_dec account (fst p)
                                            then false else true) pws
                  in ([uiEncrypt (dump pws')], uiLoop pws')

                | _ =>
                  ([uiConsoleOut "unrecognized command"], uiLoop pws)

              end

            | uiDecrypted s =>
              ([], uiLoop (load s))

          end).

Definition ui := uiLoop nil.

Require Import ExtrOcamlBasic ExtrOcamlString.
Extraction "ExamplePwMgr" ui.
