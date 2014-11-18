(* a dictionary app that displays ads related to user's input, but not the exact input *)
Require Import Ascii FunctionApp List Program.Basics String.
Import ListNotations.

Generalizable All Variables.
Class Dict k v t := 
  {
    find : k -> t -> option v
  }.

Section dict.

  Context `{Dict string string dict_t}.
  Context (content : dict_t).
  Context (world : Type).
  Context (display : string -> action world).
  Context (toAdProvider : string -> action world).

  Inductive dictInput := 
    | dictIn : string -> dictInput.

  Infix "*" := compose.

  CoFixpoint dict :=
    Step (fun i =>
            match i with
              | dictIn s =>
                match find s content with
                  | None =>
                    (display "word not found", dict)
                  | Some v =>
                    (toAdProvider v * display v, dict)
                end
            end).

End dict.


Section ad.

  Inductive adInput :=
  | adReceived : string -> adInput.

  Context (world : Type).
  Context (display : string -> action world).

  CoFixpoint ad :=
    Step (fun i =>
            match i with
              | adReceived s => (display s, ad)
            end).

End ad.


Definition getStep {input output} (p : process input output) :=
  match p with
    | Step f => f
  end.


Section sys.

  Context `{Dict string string dict_t}.
  Context (content : dict_t).
  Context (coarsen : string -> string).
  Context (world : Type).
  Context (display : string -> action world).
  Context (send : string -> action world).

  Inductive sysMessage :=
  | sysToAdProvider : string -> sysMessage.

  Inductive sysInput :=
  | sysUIIn : string -> sysInput
  | sysAdReceived : string -> sysInput.

  CoFixpoint sysLoop dict ad : stackProcess sysMessage sysInput world :=
    Step (fun i =>
            match i with
              | inl (sysToAdProvider s) =>
                (stackLift (send (coarsen s)), sysLoop dict ad)
              | inr (sysUIIn s) =>
                let (a, dict') := getStep dict (dictIn s) in (a, sysLoop dict' ad)
              | inr (sysAdReceived s) =>
                let (a, ad') := getStep ad (adReceived s) in (a, sysLoop dict ad')
            end).

  Definition
    mkSysStack
    (dict :
       forall {world'},
         (string -> action world') ->
         (string -> action world') ->
         process dictInput world')
    (ad :
       forall {world'},
         (string -> action world') ->
         process adInput world') :
    stackProcess sysMessage sysInput world :=
    sysLoop
      (dict
         (fun s => stackLift (display s))
         (fun s => stackPush (sysToAdProvider s)))
      (ad
         (fun s => stackLift (display s))).

  Definition sysStack := mkSysStack (dict content) ad.

  Definition sys : process sysInput world. 
    refine (runStackProcess sysStack _).
    admit.
  Defined.

End sys.


Require Import ExtrOcamlBasic ExtrOcamlString.
Extraction "ExampleDictWithAd" sys.
