Require Import Coq.Strings.String Coq.FSets.FMapInterface.
Require Import PrefixSerializableDefinitions.

Module Type SerializableOrderedType.
  Include OrderedType.OrderedType.
  Parameter PrefixSerializable_ord : PrefixSerializable t eq.
  Global Existing Instance PrefixSerializable_ord.
End SerializableOrderedType.

Module Type SerializableMergableMapInterface (E : SerializableOrderedType).
  Include Sfun E.


  Section elt.
    Variable elt : Type.

    Parameter Serializable_map : forall `{Serializable elt}, Serializable (t elt).
    Parameter Deserializable_map : forall `{Deserializable elt}, Deserializable (t elt).

    Local Existing Instance Serializable_map.
    Local Existing Instance Deserializable_map.
    Axiom from_to_string_map
    : forall `{PrefixSerializable elt}
             (eq_elt : relation elt),
      forall x : t elt,
        option_lift_relation (Equiv eq_elt) (fst (from_string (A := t elt) (to_string x))) (Some x)
        /\ snd (from_string (A := t elt) (to_string x)) = ""%string.
    Axiom prefix_closed_map
    : forall `{PrefixSerializable elt}
             (eq_elt : relation elt),
      forall s1 s2 x,
        option_lift_relation (Equiv eq_elt) (fst (from_string (A := t elt) s1)) (Some x)
        -> option_lift_relation (Equiv eq_elt) (fst (from_string (A := t elt) (s1 ++ s2))) (Some x)
           /\ snd (from_string (A := t elt) (s1 ++ s2)) = (snd (from_string (A := t elt) s1) ++ s2)%string.

    Definition PrefixSerializable_map {eq_elt} `{PrefixSerializable elt eq_elt} : PrefixSerializable (t elt) (Equiv eq_elt)
      := {| serialize := _;
            deserialize := _;
            from_to_string := from_to_string_map eq_elt;
            prefix_closed := prefix_closed_map eq_elt |}.

    Parameter merge : t elt -> t elt -> t elt.

    Axiom merge_In_1 : forall k m1 m2, In k m1 -> In k m2 -> In k (merge m1 m2).
    Axiom merge_In_2 : forall k m1 m2, In k (merge m1 m2) -> In k m1 \/ In k m2.
    Axiom merge_find_1 : forall k v m1 m2, find k m1 = Some v -> find k m2 = Some v -> find k (merge m1 m2) = Some v.
    Axiom merge_find_2 : forall k v m1 m2, find k m1 = None -> find k (merge m1 m2) = Some v -> find k m2 = Some v.
    Axiom merge_find_3 : forall k v m1 m2, find k m2 = None -> find k (merge m1 m2) = Some v -> find k m1 = Some v.
  End elt.

  Global Hint Extern 1 (Serializable (t _)) => apply Serializable_map : typeclass_instances.
  Global Hint Extern 1 (Deserializable (t _)) => apply Deserializable_map : typeclass_instances.
  Global Hint Extern 1 (PrefixSerializable (t _)) => apply PrefixSerializable_map : typeclass_instances.
End SerializableMergableMapInterface.
