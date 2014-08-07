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


Module Restriction.
  Definition chs : channels := fun _ => nat.

  Definition pr1 : process chs :=
    #!chs["output", 1], #!chs["output", 2], Done.

  CoFixpoint monitor : process chs :=
    #?chs["intermediate", n],
    match n with
      | O => monitor
      | _ => #!chs["output", n], monitor
    end.

  Theorem monitor_eq : monitor = #?chs["intermediate", n],
                       match n with
                         | O => monitor
                         | _ => #!chs["output", n], monitor
                       end.
  Proof.
    rewrite expand_ok at 1; auto.
  Qed.

  Definition pr2 (pr : process chs) : process chs :=
    (##[(Send, "intermediate")], pr)
    || monitor.

  Lemma pr1_pr2' : forall n k pr, refines k (pr2 pr)
    -> refines (#!chs["output", S n], k) (pr2 (#!chs["intermediate", S n], pr)).
  Proof.
    intros.
    unfold pr2.
    rewrite monitor_eq.
    apply match_right_restricted.
    simpl; tauto.
    apply send_send.
    auto.
  Qed.    

  Theorem pr1_pr2 : exists pr, refines pr1 (pr2 pr).
  Proof.
    eexists.
    repeat apply pr1_pr2'.
    instantiate (1 := Done).
    refines.
  Qed.
End Restriction.
