Require Import Coq.Strings.String.

Set Implicit Arguments.

Local Open Scope string_scope.

Class Serializable A :=
  { to_string : A -> string }.
Class Deserializable A :=
  { from_string : string -> option A * string }.

Class PrefixSerializable A :=
  { serialize :> Serializable A;
    deserialize :> Deserializable A;
    from_to_string : forall x, from_string (to_string x) = (Some x, "");
    prefix_closed : forall s1 s2 x, fst (from_string s1) = Some x -> from_string (s1 ++ s2) = (Some x, snd (from_string s1) ++ s2) }.

Arguments serialize _ !_ / .
Arguments deserialize _ !_ / .
