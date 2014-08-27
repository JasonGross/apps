Require Import Process Refinement ModelCheck.


Module Done.
  Definition chs : channels := fun _ => nat.

  Definition pr : process chs := Done.

  Theorem pr_pr : refines pr pr.
  Proof.
    refines.
  Qed.
End Done.

Module DoneSend.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := Done.

  Definition pr2 : process chs := #!chs["X", 0], Done.

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
  Qed.
End DoneSend.

Module Send.
  Definition chs : channels := fun _ => nat.

  Definition pr : process chs := #!chs["X", 0], Done.

  Theorem pr_pr : refines pr pr.
  Proof.
    refines.
    refines.
  Qed.
End Send.

Module Recv.
  Definition chs : channels := fun _ => nat.

  Definition pr : process chs := #?chs["X", x], Done.

  Theorem pr_pr : refines pr pr.
  Proof.
    refines.
    refines.
  Qed.
End Recv.

Module RecvSend.
  Definition chs : channels := fun _ => nat.

  Definition pr : process chs := #?chs["X", x], #!chs["Y", x], Done.

  Theorem pr_pr : refines pr pr.
  Proof.
    refines.
    refines.
    refines.
  Qed.
End RecvSend.

Module SwapSend.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := (#!chs["X", 0], Done) || (#!chs["Y", 1], Done).

  Definition pr2 : process chs := (#!chs["Y", 1], Done) || (#!chs["X", 0], Done).

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
    refines.
    refines.
    refines.
    refines.
  Qed.
End SwapSend.

Module SwapSendRecv.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := (#!chs["X", 0], Done) || (#?chs["Y", x], #!chs["Z", x], Done).

  Definition pr2 : process chs := (#?chs["Y", x], #!chs["Z", x], Done) || (#!chs["X", 0], Done).

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
    refines.
    refines.
    refines.
    refines.
    refines.
    refines.
    refines.
    refines.
  Qed.
End SwapSendRecv.

Module WithSelf.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := ##[(Send, "X")],
    (#?chs["Y", x], #!chs["X", S x], Done)
    || (#!chs["Y", 0], Done).

  Definition pr2 : process chs := #!chs["X", 1], Done.

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
    refines.
    refines.
  Qed.
End WithSelf.

Module WithMoreSelf.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs := ##[(Send, "X")],
    (#?chs["Y", x], #!chs["X", S x], Done)
    || (#!chs["Y", 0], Done)
    || (#!chs["Y", 1], Done).

  Definition pr2 : process chs :=
    (#!chs["X", 2], Done)
    || (#!chs["X", 1], Done).

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
    refines.
    refines.
    refines.
    refines.
  Qed.
End WithMoreSelf.

Module DependentTypingAhoy.
  Definition chs : channels := fun s => if string_dec s "B" then bool else nat.

  Definition pr1 : process chs := ##[(Recv, "B"), (Send, "X")],
    (#?chs["B", b], #?chs["N", n], if b then #!chs["X", 42], Done else #!chs["X", n], Done)
    || (#!chs["N", 13], Done).

  Definition pr2 : process chs :=
    #?chs["B", b], if b then #!chs["X", 42], Done else #!chs["X", 13], Done.

  Theorem pr1_pr2 : refines pr1 pr2.
  Proof.
    refines.
    destruct v.
    refines.
    refines.
    refines.
    refines.
    refines.
    refines.
  Qed.
End DependentTypingAhoy.

Module RecvSendRestr.
  Definition chs : channels := fun _ => nat.

  Definition pr : process chs := ##[(Recv, "X"), (Send, "Y")], #?chs["X", x], #!chs["Y", x], Done.

  Theorem pr_pr : refines pr pr.
  Proof.
    refines.
    refines.
    refines.
  Qed.
End RecvSendRestr.
