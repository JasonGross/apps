Require Import Coq.Strings.String Coq.FSets.FMapInterface.

Module Type SerializableOrderedType.
  Include OrderedType.OrderedType.
  Parameter to_string : t -> string.
  Parameter from_string : string -> option t.
  Axiom to_from_string : forall s, match from_string s with None => True | Some x => to_string x = s end.
  Axiom from_to_string : forall x, from_string (to_string x) = Some x.
End SerializableOrderedType.

Module Type SerializableMergableMapInterface (E : SerializableOrderedType).
  Include Sfun E.


  Section elt.
    Variable elt : Type.

    Parameter to_string : forall (elt_to_string : elt -> string),
                            t elt -> string.

    Parameter from_string : forall (elt_from_string : string -> option elt),
                              string -> option (t elt).

    Section laws.
      Variable elt_to_string : elt -> string.
      Variable elt_from_string : string -> option elt.

      Axiom from_to_string
      : (forall x, elt_from_string (elt_to_string x) = Some x)
        -> forall x, from_string elt_from_string (to_string elt_to_string x) = Some x.
    End laws.

    Parameter merge : t elt -> t elt -> t elt.

    Axiom merge_In_1 : forall k m1 m2, In k m1 -> In k m2 -> In k (merge m1 m2).
    Axiom merge_In_2 : forall k m1 m2, In k (merge m1 m2) -> In k m1 \/ In k m2.
    Axiom merge_find_1 : forall k v m1 m2, find k m1 = Some v -> find k m2 = None -> find k (merge m1 m2) = Some v.
    Axiom merge_find_2 : forall k v m1 m2, find k m1 = None -> find k m2 = Some v -> find k (merge m1 m2) = Some v.
  End elt.
End SerializableMergableMapInterface.
