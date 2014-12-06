Require Import Coq.Strings.String Coq.FSets.FMapInterface.
Require Import PrefixSerializableDefinitions.

Module Type SerializableOrderedType.
  Include OrderedType.OrderedType.
  Parameter PrefixSerializable_ord : PrefixSerializable t.
  Global Existing Instance PrefixSerializable_ord.
End SerializableOrderedType.

Module Type SerializableMergableMapInterface (E : SerializableOrderedType).
  Include Sfun E.


  Section elt.
    Variable elt : Type.

    Parameter PrefixSerializable_map : forall `{PrefixSerializable elt}, PrefixSerializable (t elt).
    Global Existing Instance PrefixSerializable_map.

    Parameter merge : t elt -> t elt -> t elt.

    Axiom merge_In_1 : forall k m1 m2, In k m1 -> In k m2 -> In k (merge m1 m2).
    Axiom merge_In_2 : forall k m1 m2, In k (merge m1 m2) -> In k m1 \/ In k m2.
    Axiom merge_find_1 : forall k v m1 m2, find k m1 = Some v -> find k m2 = None -> find k (merge m1 m2) = Some v.
    Axiom merge_find_2 : forall k v m1 m2, find k m1 = None -> find k m2 = Some v -> find k (merge m1 m2) = Some v.
  End elt.
End SerializableMergableMapInterface.
