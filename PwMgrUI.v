(** * A UI Box for the PWMgr, which uses proven-correct (de)serialization code *)
Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Program.Basics Coq.Program.Program Coq.Strings.String Coq.Classes.RelationClasses.
Require Import FunctionApp SerializableMergableFMapInterface StringKey PrefixSerializable.
Import ListNotations.
Open Scope string_scope.

Module String_as_SOT <: SerializableOrderedType.
  Include String_as_OT.
  Global Instance PrefixSerializable_ord : PrefixSerializable t eq
    := _ : PrefixSerializable string Coq.Init.Logic.eq.
  Global Instance eq_Reflexive : Reflexive eq := eq_refl.
  Global Instance eq_Symmetric : Symmetric eq := eq_sym.
  Global Instance eq_Transitive : Transitive eq := eq_trans.
End String_as_SOT.

Module PwMgrUI (KVStore : SerializableMergableMapInterface String_as_SOT).
  Section ui.

    Inductive uiInput :=
    | uiConsoleIn (line : string)
    | uiGotUpdate (data : string).

    Inductive uiOutput :=
    | uiGetUpdate
    | uiSetData (data : string)
    | uiConsoleOut (lines : string).

    Context (world : Type)
            (handle : uiOutput -> action world).

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

    Definition uiLoopBody (uiLoop : KVStore.t string -> process uiInput world) (pws : KVStore.t string)
    : uiInput -> action world * process uiInput world
      := (fun i =>
            match i with
              | uiConsoleIn s =>
                match split " " s with
                  | comm :: ls =>
                    match string_dec comm "get", ls with
                      | left _, account :: nil =>
                        match KVStore.find account pws with
                          | None =>
                            (handle (uiConsoleOut "account not found"), uiLoop pws)
                          | Some password =>
                            (handle (uiConsoleOut password), uiLoop pws)
                        end
                      | _, _ =>
                        match string_dec comm "set", ls with
                          | left _,  account :: password :: nil =>
                            let pws' := KVStore.add account password pws in
                            (handle (uiSetData (to_string pws')), uiLoop pws')

                          | _, _ =>
                            (handle (uiConsoleOut "unrecognized command"), uiLoop pws)
                        end
                    end
                  | _ => (handle (uiConsoleOut "unrecognized command"), uiLoop pws)
                end
              | uiGotUpdate s =>
                let left_over := snd (from_string (A := KVStore.t string) s) in
                let action := (if string_dec left_over ""
                               then id
                               else handle (uiConsoleOut ("extra deserialization garbage: '" ++ left_over ++ "'"))) in
                match fst (from_string (A := KVStore.t string) s) with
                  | Some new_pws
                    => let pws' := KVStore.merge _ pws new_pws in
                       ((if KVStore.equal (fun s1 s2 => if string_dec s1 s2 then true else false) pws pws'
                         then action
                         else (action ∘ handle (uiSetData (to_string pws')))),
                        uiLoop pws')
                  | None => ((handle (uiConsoleOut ("non-deserializable network response: '" ++ s ++ "'")))
                               ∘ (handle (uiSetData (to_string pws))),
                             uiLoop pws)
                end
            end).

    CoFixpoint uiLoop (pws : KVStore.t string) :=
      Step (uiLoopBody uiLoop pws).


    Definition ui := uiLoop (KVStore.empty _).

  End ui.
End PwMgrUI.
