Require Import Coq.FSets.FMapAVL Coq.FSets.FMapInterface.
Require Import System AESGCM SerializableMergableFMapInterface SerializableMergableFMapImplementation PwMgrUI ExamplePwMgrWithSSB.

Module PreKVStore <: FMapInterface.Sfun String_as_SOT := FMapAVL.Make String_as_SOT.
Module KVStore <: SerializableMergableMapInterface String_as_SOT := MakeSerializableMergableMap String_as_SOT PreKVStore.

Module Export PwMgr := MakePwMgr KVStore AESGCM.

Module Application.
  Include System.
  Include PwMgr.
End Application.

Require Import ExtrOcamlBasic ExtrOcamlString.
Extraction "ExamplePwMgrWithSSBFull" Application.
