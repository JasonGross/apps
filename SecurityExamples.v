Require Import Arith Process Refinement ModelCheck.


Definition chs : channels := fun _ => nat.

(* Policy: Process may only send on channel "out". *)
Module SendOnlyOnOut.
  Definition policy (pr : process chs) : process chs :=
    ##[(Send, "out")], pr.

  Definition impl : process chs :=
    #!chs["out", 1], Done.

  Theorem conforms : exists pr, refines impl (policy pr).
  Proof.
    exists impl.
    refines.
    refines.
  Qed.
End SendOnlyOnOut.

(* Policy: Process should only send a number less than or equal to 5. *)
Module SendLe5.
  Definition policy (pr : process chs) : process chs :=
    (##[(Send, "tmp")], pr) || (#?chs["tmp", n], if leb n 5 then #!chs["out", n], Done else Done).

  Definition impl : process chs :=
    #!chs["out", 4], Done.

  Theorem conforms : exists pr, refines impl (policy pr).
  Proof.
    exists (#!chs["tmp", 4], Done).
    refines.
    refines.
    refines.
  Qed.
End SendLe5.

(* Policy: Process receives two numbers and is only allowed to depend on their sum. *)
Module OnlySum.
  Definition policy (pr : process chs) : process chs := ##[(Recv, "in"), (Send, "out")],
    (##[(Recv, "tmp"), (Send, "out")], pr) || (#?chs["in", n], #?chs["in", m], #!chs["tmp", n + m], Done).

  Definition impl : process chs :=
    #?chs["in", n], #?chs["in", m], #!chs["out", 3 + (n + m)], Done.

  Theorem conforms : exists pr, refines impl (policy pr).
  Proof.
    exists (#?chs["tmp", sum], #!chs["out", 3 + sum], Done).
    refines.
    refines.
    refines.
    refines.
    refines.
  Qed.
End OnlySum.
