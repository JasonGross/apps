(** * Coq Framework for security policies and proof of concept application - Guide *)
(** 6.858 Project by Anders Kaseorg, Jason Gross, and Peng Wang *)
(** ** Trusted Code *)
(** *** The Framework Definitions *)
Require FunctionApp.
(** *** The Encryption Algorithm *)
Require AES GCM AESGCM.
(** *** The Encryption/Decryption Boxes *)
Require TrustedEncryptBox TrustedDecryptBox EncryptionInterface.
(** *** The Tick Box (Timing Side-Channel Avoidance Box) *)
Require TrustedTickBox.
(** *** The Server Box that puts together the encryption, decryption, and tick boxes *)
Require TrustedServerSyncBox.
(** *** The top-level wiring diagram *)
Require ExamplePwMgrWithSSB ExamplePwMgrWithSSBFull.
(** *** The trusted OCaml shims *)
(** We trust [ExamplePwMgrWithSSBFullRuntime.ml] and [Runtime.ml] *)

(** ** Semi-trusted Code *)
(** *** Display of warnings *)
(** We don't leak any information if we hide warnings from the user,
    but it's not a completely innocuous operation either. *)
Require PwMgrWarningBox.

(** ** Untrusted Code *)
(** *** Proven-correct Serialization and Deserialization *)
(** Waaaay too much code here. *)
Require PrefixSerializableDefinitions PrefixSerializable.
(** *** Proven-correct [FMapInterface] that is also mergable and (de)serializable *)
Require SerializableMergableFMapInterface SerializableMergableFMapImplementation.
(** *** UI Code *)
Require PwMgrUI.
(** *** HTTPS Code *)
Require PwMgrNet.
