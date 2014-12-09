(** * A Box to emit warnings for the PWMgr *)
Require Import Coq.Program.Program Coq.Strings.String.
Require Import FunctionApp TrustedServerSyncBox EncryptionInterface TrustedTickBox PrefixSerializable.

Local Open Scope string_scope.

Module PwMgrWarningBox (Algorithm : EncryptionAlgorithm EncryptionStringDataTypes).
  Module SSB := TrustedServerSyncBox EncryptionStringDataTypes Algorithm.

  Section warnings.

    Definition wInput : Type := SSB.ssbWarningOutput.

    (** [wConsoleErr] is a valid warning message outside of our
         control, like that the server got corrupted or the user typed
         garbage.

         [wBad] is an event that should never be fired.  It should
         probably be hooked into a loop, and shown not to exist via
         the termination proof. *)
    Inductive wOutput :=
    | wConsoleErr (lines : string)
    | wBad (msg : string).

    Context (world : Type)
            (handle : wOutput -> action world).

    (*efinition newline := "010"%char.*)

    Definition emit (body : string) : action world
      := handle (wConsoleErr ("WARNING: " ++ body)).

    Definition emitTB {T} (ev : tbWarningOutput T) (component : string) : action world
      := let pre := ("In component '" ++ component ++ "', ") in
         match ev with
           | tbWarnNoDataReady => handle (wBad (pre ++ "data was not ready to send"))
           | tbWarnTicksTooInfrequent => emit (pre ++ "tick starvation is occuring")
           | tbWarnInvalidWaitBeforeUpdateInterval n => handle (wBad (pre ++ "invalid wait"))
           | tbWarnInvalidEvent st ev' => handle (wBad (pre ++ "invalid event"))
         end.

    Definition wLoopBody (wLoop : unit -> process wInput world) (st : unit)
    : wInput -> action world * process wInput world
      := fun i =>
           match i with
             | SSB.ssbGetUpdateWarning ev
               => (emitTB ev "Get Update Box", wLoop st)
             | SSB.ssbCASWarning ev
               => (emitTB ev "Compare And Set Box", wLoop st)
             | SSB.ssbWarningPushBeforePull
               => (emit "Cannot do a server-compare-and-swap before obtaining server's current state",
                   wLoop st)
             | SSB.ssbEncryptError (SSB.TEB.ebErrorNotEnoughRandomness howMuch given)
               (* we should use a better [nat -> string] here, that isn't binary *)
               => (handle (wConsoleErr ("Not enough randomness: wanted " ++ (to_string howMuch) ++ ", but got the string: '" ++ given ++ "'")),
                   wLoop st)
             | SSB.ssbEncryptError (SSB.TEB.ebErrorInvalidMasterKey key pf)
               => (handle (wBad ("Invalid Master Key in encryption box: " ++ key)),
                   wLoop st)
             | SSB.ssbEncryptError SSB.TEB.ebErrorNoMasterKey
               (* is this [wBad], or just [wConsoleErr]? *)
               => (handle (wBad "No Master Key in encryption box"),
                   wLoop st)
             | SSB.ssbDecryptError (SSB.TDB.dbErrorInvalidMasterKey key pf)
               => (handle (wBad ("Invalid Master Key in decryption box: " ++ key)),
                   wLoop st)
             | SSB.ssbDecryptError SSB.TDB.dbErrorNoMasterKey
               (* is this [wBad], or just [wConsoleErr]? *)
               => (handle (wBad "No Master Key in decryption box"),
                   wLoop st)
             | SSB.ssbDecryptError (SSB.TDB.dbErrorInvalidData data tt)
               => (handle (wConsoleErr ("Server got corrupted - encrypted data recieved is: " ++ data)),
                   wLoop st)
             | SSB.ssbWarningInvalidTransition ev' st'
               => (handle (wBad "Server Sync Box invalid transition"), wLoop st)
           end.

    CoFixpoint wLoop (st : unit) :=
      Step (wLoopBody wLoop st).

    Definition warningBox := wLoop tt.

  End warnings.
End PwMgrWarningBox.
