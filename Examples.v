Require Import Process Refinement.


Module OnlyPositive.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs :=
    #?chs["input", n],
    match n with
    | O => Done
    | _ => #!chs["output", n], Done
    end.

  Definition pr2 : process chs :=
    (#?chs["input", n],
     match n with
     | O => Done
     | _ => #!chs["intermediate", n], Done
     end)
    || (#?chs["intermediate", n], #!chs["output", n], Done).

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
    destruct v; refines.
  Qed.
End OnlyPositive.
