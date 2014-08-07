Require Import Process Eqdep_dec.


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

  Theorem pr1_pr2 : refines (fun s => s = "input" \/ s = "output") pr1 pr2.
  Proof.
    hnf; intros.
    inversion H; clear H; subst; eauto.
    apply (inj_pair2_eq_dec _ string_dec) in H2; subst.
    destruct v.
    inversion H3; clear H3; subst.
    eexists; split.
    econstructor.
    econstructor.
    instantiate (2 := O); simpl.
    eauto.
    eauto.
    eauto.
    eauto 10.

    inversion H3; clear H3; subst.
    Focus 2.
    eexists; split.
    econstructor.
    repeat econstructor.
    apply TrDone.
    eauto.
    eauto 10.

    apply (inj_pair2_eq_dec _ string_dec) in H1; subst.
    inversion H4; clear H4; subst.
    eexists; split.
    econstructor.
    econstructor.
    instantiate (2 := S v); simpl.
    econstructor.
    eauto.
    econstructor.
    econstructor.
    econstructor.
    apply IntCons1.
    apply IntMatch1.
    eauto.
    eapply TrSome; eauto.
    eapply TrSome; eauto.
  Qed.
End OnlyPositive.
