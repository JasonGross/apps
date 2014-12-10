(** * A Box to emit warnings for the PWMgr *)
Require Import Coq.NArith.BinNat Coq.Program.Program Coq.Strings.String.
Require Import FunctionApp TrustedServerSyncBox EncryptionInterface TrustedTickBox PrefixSerializable.
Require Import TrustedTickBoxPrefixSerializable.

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
         the termination proof.

         [wFatalError] is a state that's possible, but should kill the
         program. *)
    Inductive wOutput :=
    | wConsoleErr (lines : string)
    | wFatalError (lines : string)
    | wBad (msg : string).

    Context (world : Type)
            (handle : wOutput -> action world).

    Definition newline := "010"%char.
    Definition newlineS := String newline "".

    Definition emit (body : string) : action world
      := handle (wConsoleErr ("WARNING: " ++ body)).

    Definition debug (component body : string) : action world
      := handle (wConsoleErr ("DEBUG (" ++ component ++ "): " ++ body)).

    Definition labelTBStateTransition {T} `{Serializable T} (old new : TrustedTickBox.TickBoxPreState T) (ev : TrustedTickBox.tbInput T)
    : string
      := "from" ++ newlineS ++ "  " ++ to_string old ++ newlineS ++ "to (" ++ to_string ev ++ ")" ++ newlineS ++ "  " ++ to_string new.

    Definition emitTB {T} `{Serializable T} (ev : tbWarningOutput T) (component : string) : action world
      := let pre := ("In component '" ++ component ++ "', ") in
         match ev with
           | tbWarnNoDataReady => handle (wBad (pre ++ "data was not ready to send"))
           | tbWarnTicksTooInfrequent ticks => emit (pre ++ "tick starvation is occuring: " ++ to_string ticks)
           | tbWarnInvalidWaitBeforeUpdateInterval n => handle (wBad (pre ++ "invalid wait"))
           | tbWarnInvalidEvent st ev' => handle (wBad (pre ++ "invalid event"))
           | tbDebugStateTransition old new ev' => debug component (labelTBStateTransition (T := T) old new ev')
         end.

    Definition wLoopBody (wLoop : N -> process wInput world) (debug : N)
    : wInput -> action world * process wInput world
      := fun i =>
           match i with
             | SSB.ssbGetUpdateWarning ev
               => (emitTB ev "Get Update Box", wLoop debug)
             | SSB.ssbCASWarning ev
               => (emitTB ev "Compare And Set Box", wLoop debug)
             | SSB.ssbWarningPushBeforePull
               => (emit "Cannot do a server-compare-and-swap before obtaining server's current state",
                   wLoop debug)
             | SSB.ssbEncryptError (SSB.TEB.ebErrorNotEnoughRandomness howMuch given)
               (* we should use a better [nat -> string] here, that isn't binary *)
               => (handle (wConsoleErr ("Not enough randomness: wanted " ++ (to_string howMuch) ++ ", but got the string: '" ++ given ++ "'")),
                   wLoop debug)
             | SSB.ssbEncryptError (SSB.TEB.ebErrorInvalidMasterKey key pf)
               => (handle (wFatalError ("Invalid Master Key: " ++ key)),
                   wLoop debug)
             | SSB.ssbEncryptError SSB.TEB.ebErrorNoMasterKey
               (* is this [wBad], or just [wConsoleErr]? *)
               => (handle (wBad "No Master Key in encryption box"),
                   wLoop debug)
             | SSB.ssbDecryptError (SSB.TDB.dbErrorInvalidMasterKey key pf)
               => (handle (wFatalError ("Invalid Master Key: " ++ key)),
                   wLoop debug)
             | SSB.ssbDecryptError SSB.TDB.dbErrorNoMasterKey
               (* is this [wBad], or just [wConsoleErr]? *)
               => (handle (wBad "No Master Key in decryption box"),
                   wLoop debug)
             | SSB.ssbDecryptError (SSB.TDB.dbErrorInvalidData data tt)
               => (handle (wConsoleErr ("Server got corrupted - encrypted data recieved is: " ++ data)),
                   wLoop debug)
             | SSB.ssbWarningInvalidTransition ev' st'
               => (handle (wBad "Server Sync Box invalid transition"), wLoop debug)
           end.

    CoFixpoint warningBox (debug : N) :=
      Step (wLoopBody warningBox debug).

  End warnings.
End PwMgrWarningBox.
