Require Import List Permutation Process Eqdep_dec.


Ltac my_subst := repeat match goal with
                        | [ x : _ |- _ ] => subst x
                        end.

Ltac inv H := inversion H; clear H; my_subst;
              repeat match goal with
                     | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
                       apply (inj_pair2_eq_dec _ string_dec) in H; my_subst
                     end; simpl in *.

Section Refinement.
  Variable chs : channels.

  (** A normal form for processes *)

  CoInductive proc0 :=
  | NSend (ch : channel) (v : chs ch) (k : proc0)
  | NRecv (ch : channel) (k : chs ch -> proc0)
  | NDone.

  Record proc := {
    Chans : direction * channel -> Prop;
    Code : proc0
  }.

  Record procs := {
    TopChans : direction * channel -> Prop;
    Procs : list proc
  }.

  CoFixpoint proc0D (p : proc0) : process chs :=
    match p with
    | NSend ch v k => DoSend ch v (proc0D k)
    | NRecv ch k => DoRecv ch (fun v => proc0D (k v))
    | NDone => Done
    end.

  Definition procD (p : proc) : process chs :=
    Restrict (Chans p) (proc0D (Code p)).

  Fixpoint procsD' (ps : list proc) : process chs :=
    match ps with
    | nil => Done
    | p :: ps' => Parallel (procD p) (procsD' ps')
    end.

  Definition procsD (ps : procs) : process chs :=
    Restrict (TopChans ps) (procsD' (Procs ps)).

  Definition norm (p : process chs) (ps : procs) : Prop :=
    refines p (procsD ps)
    /\ refines (procsD ps) p.

  Inductive normalize : process chs -> proc0 -> Prop :=
  | InSend : forall ch v k k', normalize k k'
    -> normalize (DoSend ch v k) (NSend ch v k')
  | InRecv : forall ch k k', (forall v, normalize (k v) (k' v))
    -> normalize (DoRecv ch k) (NRecv ch k')
  | InDone : normalize Done NDone
  | InIf : forall (b : bool) k1 k1' k2 k2', normalize k1 k1'
    -> normalize k2 k2'
    -> normalize (if b then k1 else k2) (if b then k1' else k2').

  Lemma expand_proc0D : forall p, proc0D p = expand (proc0D p).
  Proof.
    intros.
    rewrite <- expand_ok.
    auto.
  Qed.

  Lemma normalize_fwd : forall p p', normalize p p'
    -> forall tr, traceOf p tr
      -> traceOf (proc0D p') tr.
  Proof.
    induction 1; simpl; eauto; inversion 1; subst; eauto.
    apply (inj_pair2_eq_dec _ string_dec) in H3; subst.
    rewrite expand_proc0D; simpl; eauto.
    apply (inj_pair2_eq_dec _ string_dec) in H4; subst.
    inv H1; eauto.
    rewrite expand_proc0D; simpl; eauto.
    destruct b; subst; eauto.
    destruct b; subst; eauto.
    destruct b; subst; eauto.
    destruct b; subst; eauto.
  Qed.

  Lemma normalize_bwd : forall p p', normalize p p'
    -> forall tr, traceOf (proc0D p') tr
      -> traceOf p tr.
  Proof.
    induction 1; simpl; eauto; inversion 1; simpl; intros; eauto;
    try match goal with
        | [ H : _ = proc0D _ |- _ ] => rewrite expand_proc0D in H; simpl in H; inv H; eauto
        end.
    destruct b; eauto.
    destruct b; eauto.
    destruct b; eauto.
    destruct b; eauto.
  Qed.

  Lemma traceAll_True : forall p, traceAll (chs := chs) (fun _ => True) p.
  Proof.
    induction p; auto.
  Qed.

  Hint Resolve traceAll_True.

  Lemma interleave_nil1' : forall nl tr1 tr2,
    interleave (chs := chs) nl tr1 tr2
    -> nl = nil
    -> tr1 = tr2.
  Proof.
    induction 1; simpl; intros; intuition; try congruence.
  Qed.

  Lemma interleave_nil1 : forall tr1 tr2,
    interleave (chs := chs) nil tr1 tr2
    -> tr1 = tr2.
  Proof.
    eauto using interleave_nil1'.
  Qed.

  Lemma interleave_sym : forall tr1 tr2 tr3,
    interleave (chs := chs) tr1 tr2 tr3
    -> interleave tr2 tr1 tr3.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma interleave_nil2 : forall tr1 tr2,
    interleave (chs := chs) tr1 nil tr2
    -> tr1 = tr2.
  Proof.
    intros; apply interleave_nil1; apply interleave_sym; auto.
  Qed.

  Theorem normBasic : forall p p', normalize p p'
    -> norm p {| TopChans := fun _ => True;
                 Procs := {| Chans := fun _ => True; Code := p' |} :: nil |}.
  Proof.
    split; unfold procsD, procD; simpl.

    do 2 intro.
    econstructor.
    econstructor.
    2: eauto.
    2: eauto.
    econstructor.
    eauto using normalize_fwd.
    auto.
    eauto.

    do 2 intro.
    inv H0; eauto.
    inv H3; eauto.
    inv H2.
    inv H4.
    apply interleave_nil2 in H7; subst.
    eauto using normalize_bwd.
    inv H4.
    apply interleave_nil2 in H7; subst; eauto.
  Qed.

  Theorem Parallel_comm : forall p1 p2,
    refines (chs := chs) (p1 || p2) (p2 || p1).
  Proof.
    do 4 intro.
    inv H; eauto using interleave_sym.
  Qed.

  Ltac reassoc1 :=
    try match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
        end;
    try match goal with
        | [ IHinterleave : forall tr3 tr3 : trace chs, _, H : interleave _ _ _ |- _ ] =>
          apply IHinterleave in H; clear IHinterleave; firstorder
        end;
    try match goal with
        | [ H : _ = _ -> ex _ |- _ ] => destruct H; intuition; []
        end;
    try solve [ do 2 esplit; [ solve [ econstructor; eauto | apply IntCons2; eauto ] | eauto ] ].

  Ltac induct :=
    match goal with
    | [ H : interleave _ _ ?ls |- _ ] =>
      remember ls; induction H; subst; eauto; try congruence
    end.

  Ltac reassoc := solve [ reassoc1 ] || (induct; reassoc1).

  Lemma interleave_reassoc1 : forall tr3 tr tr',
    interleave (chs := chs) tr3 tr tr'
    -> forall tr1 tr2, interleave (chs := chs) tr1 tr2 tr
    -> exists tr'', interleave tr3 tr1 tr'' /\ interleave tr'' tr2 tr'.
  Proof.
    induction 1; eauto; intros; reassoc.
  Qed.

  Theorem Parallel_assoc1 : forall p1 p2 p3,
    refines (chs := chs) (p1 || (p2 || p3)) ((p1 || p2) || p3).
  Proof.
    do 5 intro.
    inv H; eauto.
    inv H3; eauto.
    eapply interleave_reassoc1 in H7; try apply H5; firstorder.
    eauto.
  Qed.

  Lemma interleave_reassoc2 : forall tr3 tr tr',
    interleave (chs := chs) tr tr3 tr'
    -> forall tr1 tr2, interleave (chs := chs) tr1 tr2 tr
    -> exists tr'', interleave tr2 tr3 tr'' /\ interleave tr1 tr'' tr'.
  Proof.
    induction 1; eauto; intros; reassoc.
  Qed.

  Theorem Parallel_assoc2 : forall p1 p2 p3,
    refines (chs := chs) ((p1 || p2) || p3) (p1 || (p2 || p3)).
  Proof.
    do 5 intro.
    inv H; eauto.
    inv H2; eauto.
    eapply interleave_reassoc2 in H7; try apply H5; firstorder eauto.
  Qed.

  Lemma Parallel_cong : forall p q p' q',
    refines (chs := chs) p p'
    -> refines q q'
    -> refines (p || q) (p' || q').
  Proof.
    unfold refines; intros.
    inv H1; eauto.
  Qed.

  Lemma refines_Restrict_True1 : forall p,
    refines (chs := chs) p (Restrict (fun _ => True) p).
  Proof.
    do 3 intro.
    eauto.
  Qed.

  Lemma refines_Restrict_True2 : forall p,
    refines (chs := chs) (Restrict (fun _ => True) p) p.
  Proof.
    do 3 intro.
    inv H; eauto.
  Qed.
  
  Lemma refines_trans : forall p q r, refines (chs := chs) p q
    -> refines q r
    -> refines p r.
  Proof.
    firstorder.
  Qed.

  Lemma procsD_app1' : forall ps2 ps1,
    refines (procsD' (ps1 ++ ps2))
            (Parallel (procsD' ps1) (procsD' ps2)).
  Proof.
    intros; induction ps1; simpl; hnf; intros; eauto.
    apply Parallel_assoc1.
    inv H; eauto.
  Qed.

  Lemma procsD_app1 : forall ps2 ps1,
    refines (procsD {| TopChans := fun _ => True; Procs := ps1 ++ ps2|})
            (Parallel (procsD {| TopChans := fun _ => True; Procs := ps1 |})
                      (procsD {| TopChans := fun _ => True; Procs := ps2 |})).
  Proof.
    unfold procsD; simpl; intros.
    eapply refines_trans; [ apply refines_Restrict_True2 | ].
    eapply refines_trans; [ | apply Parallel_cong; apply refines_Restrict_True1 ].
    apply procsD_app1'.
  Qed.

  Lemma procsD_app2' : forall ps2 ps1,
    refines (Parallel (procsD' ps1) (procsD' ps2)) (procsD' (ps1 ++ ps2)).
  Proof.
    induction ps1; simpl; hnf; intros; eauto.

    inv H; eauto.
    inv H2; eauto.
    apply interleave_nil1 in H5; congruence.

    apply Parallel_assoc2 in H.
    inv H; eauto.
  Qed.

  Lemma procsD_app2 : forall ps2 ps1,
    refines (Parallel (procsD {| TopChans := fun _ => True; Procs := ps1 |})
                      (procsD {| TopChans := fun _ => True; Procs := ps2 |}))
            (procsD {| TopChans := fun _ => True;
                       Procs := ps1 ++ ps2 |}).
  Proof.
    unfold procsD; simpl; intros.
    eapply refines_trans; [ | apply refines_Restrict_True1 ].
    eapply refines_trans; [ apply Parallel_cong; apply refines_Restrict_True2 | ].
    apply procsD_app2'.
  Qed.

  Lemma normProc0D : forall p, norm (proc0D p) {| TopChans := fun _ => True;
                                                  Procs := {| Chans := fun _ => True;
                                                              Code := p |} :: nil |}.
  Proof.
    unfold norm, refines; simpl; intuition.
    econstructor; eauto; simpl.
    econstructor.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.

    inv H; eauto.
    inv H2; eauto.
    inv H1; eauto.
    inv H3.
    apply interleave_nil2 in H6; subst; eauto.
    apply interleave_nil1 in H6; subst; eauto.
    inv H3; eauto.
  Qed.

  Lemma normProcD : forall p, norm (procD p) {| TopChans := fun _ => True; Procs := p :: nil |}.
  Proof.
    unfold norm, refines; simpl; intuition.
    econstructor; eauto; simpl.
    eauto.
    inv H; eauto.
    inv H2; eauto.
    inv H3.
    apply interleave_nil2 in H6; subst; eauto.
  Qed.

  Lemma normShift : forall p p' P, norm p {| TopChans := P; Procs := {| Chans := fun _ => True; Code := p' |} :: nil |}
    -> norm p {| TopChans := fun _ => True; Procs := {| Chans := P; Code := p' |} :: nil |}.
  Proof.
    unfold norm, refines; simpl; intuition.

    apply H0 in H.
    inv H; eauto.
    inv H4; eauto.
    inv H5.
    apply interleave_nil2 in H8; subst.
    inv H3; eauto.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.

    apply H1.
    inv H; eauto.
    inv H4; eauto.
    inv H5.
    apply interleave_nil2 in H8; subst.
    inv H3; eauto.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
  Qed.

  Theorem normParallel : forall p1 ps1 p2 ps2, norm p1 {| TopChans := fun _ => True; Procs := ps1 |}
    -> norm p2 {| TopChans := fun _ => True; Procs := ps2 |}
    -> norm (Parallel p1 p2) {| TopChans := fun _ => True; Procs := ps1 ++ ps2 |}.
  Proof.
    split; simpl; do 2 intro.

    apply procsD_app2.
    unfold norm, refines in *.
    intuition.
    inv H1; eauto.

    apply procsD_app1 in H1.
    unfold norm, refines in *.
    intuition.
    inv H1; eauto.
  Qed.

  Lemma traceAll_and : forall P1 P2 tr,
    traceAll (chs := chs) P1 tr
    -> traceAll P2 tr
    -> traceAll (fun x => P1 x /\ P2 x) tr.
  Proof.
    induction 1; inversion 1; subst; eauto.
    constructor; intuition.
  Qed.

  Lemma traceAll_weaken : forall (P1 P2 : _ -> Prop),
    (forall x, P1 x -> P2 x)
    -> forall ps, traceAll (chs := chs) P1 ps
      -> traceAll P2 ps.
  Proof.
    induction 2; eauto.
  Qed.

  Theorem normRestrictTrivial : forall p ps,
    norm p ps
    -> norm (Restrict (fun _ => True) p) ps.
  Proof.
    unfold norm, refines; intuition.
    inv H; eauto.
  Qed.

  Theorem normRestrictMany : forall P p ps,
    norm p {| TopChans := fun _ => True; Procs := ps |}
    -> norm (Restrict P p) {| TopChans := P; Procs := ps |}.
  Proof.
    unfold norm, refines; intuition.

    inv H; eauto.
    apply H0 in H4.
    inv H4; eauto.
    econstructor; eauto.

    inv H; eauto.
    econstructor; eauto.
    apply H1.
    econstructor; eauto.
  Qed.

  Theorem normRestrict1 : forall (P : _ -> Prop) p p',
    norm p {| TopChans := fun _ => True; Procs := {| Chans := fun _ => True; Code := p' |} :: nil |}
    -> norm (Restrict P p) {| TopChans := fun _ => True;
                              Procs := {| Chans := P; Code := p' |} :: nil |}.
  Proof.
    unfold norm, refines, procsD, procD; simpl; unfold procD; simpl; intuition.

    inv H; eauto.
    apply H0 in H4; clear H0.
    inv H4; eauto.
    inv H2; eauto.
    inv H4.
    apply interleave_nil2 in H8; subst.
    inv H3; eauto.

    inv H; eauto.
    inv H4; eauto.
    inv H5.
    apply interleave_nil2 in H8; subst.
    inv H3; eauto.
    econstructor; try eassumption.
    eauto.
  Qed.

  Theorem refines_normalize : forall p1 p2 ps1 ps2,
    norm p1 ps1
    -> norm p2 ps2
    -> refines (procsD ps1) (procsD ps2)
    -> refines p1 p2.
  Proof.
    firstorder.
  Qed.


  (** * One step of a refinement proof between two normalized processes *)

  Open Scope list_scope.

  Lemma refines_refl : forall p, refines (chs := chs) p p.
  Proof.
    firstorder.
  Qed.

  (* Recharacterize when a process system steps. *)
  Lemma whenStep' : forall ps tr, traceOf (procsD' ps) tr
    -> (* Trace ends *)
    tr = nil

    \/ (* Send *)
    (exists tr' P ch v k ps', Permutation ps ({| Chans := P; Code := NSend ch v k |} :: ps')
      /\ tr = (Send, existT _ ch v) :: tr'
      /\ P (Send, ch)
      /\ traceOf (procsD' ({| Chans := P;
                             Code := k |} :: ps')) tr')

    \/ (* Recv *)
    (exists tr' P ch v k ps', Permutation ps ({| Chans := P; Code := NRecv ch k |} :: ps')
      /\ tr = (Recv, existT _ ch v) :: tr'
      /\ P (Recv, ch)
      /\ traceOf (procsD' ({| Chans := P;
                             Code := k v |} :: ps')) tr')

    \/ (* Rendezvous *)
    (exists P1 P2 ch v k1 k2 ps',
       Permutation ps ({| Chans := P1; Code := NSend ch v k1 |}
                         :: {| Chans := P2; Code := NRecv ch k2 |} :: ps')
       /\ P1 (Send, ch)
       /\ P2 (Recv, ch)
       /\ traceOf (procsD' ({| Chans := P1;
                              Code := k1 |}
                             :: {| Chans := P2;
                                   Code := k2 v |}
                             :: ps')) tr).
  Proof.
    induction ps; simpl; intuition.

    inv H; eauto.

    inv H; eauto.
    unfold procD in H2; simpl in H2.
    inv H2; eauto.

    Focus 2.
    apply interleave_nil1 in H5; subst.
    apply IHps in H3; clear IHps; firstorder.
    
    right; left.
    repeat esplit.
    2: eauto.
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    inv H2; eauto.

    do 2 right; left.
    repeat esplit.
    2: eauto.
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    inv H2; eauto.

    do 3 right.
    repeat esplit.
    eapply perm_trans; [ | eapply perm_skip; eapply perm_swap ].
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    eauto.
    inv H2; eauto.
    inv H6; eauto.

    destruct H5.

    (* IntNil1 *)

    apply IHps in H3; clear IHps; firstorder.

    right; left.
    repeat esplit.
    2: eauto.
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    inv H3; eauto.

    do 2 right; left.
    repeat esplit.
    2: eauto.
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    inv H3; eauto.

    do 3 right.
    repeat esplit.
    eapply perm_trans; [ | eapply perm_skip; eapply perm_swap ].
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    eauto.
    inv H3; eauto.
    inv H8; eauto.

    (* IntNil2 *)

    destruct a; simpl in *.
    destruct Code0; rewrite expand_proc0D in *; simpl in *.

    inv H1; eauto.
    right; left.
    repeat esplit; eauto.
    inv H6.
    eauto.
    unfold procD; simpl.
    inv H6; eauto.

    inv H1; eauto.
    do 2 right; left.
    repeat esplit; eauto.
    inv H6.
    eauto.
    unfold procD; simpl.
    inv H6; eauto.

    inv H1; eauto.

    (* IntCons1 *)

    destruct a; simpl in *.
    destruct Code0; rewrite expand_proc0D in *; simpl in *.

    inv H1; eauto.
    right; left.
    repeat esplit; eauto.    inv H6.
    eauto.
    unfold procD; simpl.
    inv H6; eauto.

    inv H1; eauto.
    do 2 right; left.
    repeat esplit; eauto.
    inv H6.
    unfold procD; simpl.
    eauto.
    inv H6; eauto.
    econstructor.
    econstructor; eauto.
    eauto.
    eauto.

    inv H1; eauto.

    (* IntCons2 *)

    apply IHps in H3; clear IHps; firstorder; try congruence.
    
    inv H0.
    right; left.
    repeat esplit.
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    simpl.
    inv H3; eauto.
    Focus 2.
    apply interleave_nil2 in H5; subst; eauto.
    econstructor.
    apply TrDone.
    2: eauto.
    econstructor.
    econstructor.
    eauto.
    eauto.
    apply TrDone.
    auto.

    apply Parallel_assoc2.
    eapply Parallel_cong.
    apply Parallel_comm.
    apply refines_refl.
    apply Parallel_assoc1.
    econstructor.
    econstructor; eauto.
    econstructor; eauto.
    eauto.

    inv H0.
    do 2 right; left.
    repeat esplit.
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    simpl.
    inv H3; eauto.
    Focus 2.
    apply interleave_nil2 in H5; subst; eauto.
    econstructor.
    apply TrDone.
    2: eauto.
    econstructor.
    econstructor.
    eauto.
    eauto.
    apply TrDone.
    auto.

    apply Parallel_assoc2.
    eapply Parallel_cong.
    apply Parallel_comm.
    apply refines_refl.
    apply Parallel_assoc1.
    econstructor.
    econstructor; eauto.
    econstructor; eauto.
    eauto.

    do 3 right.
    repeat esplit.
    eapply perm_trans; [ | eapply perm_skip; eapply perm_swap ].
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    eauto.
    simpl.
    apply Parallel_assoc2.
    apply Parallel_comm.
    apply Parallel_assoc1.
    eapply Parallel_cong.
    apply refines_refl.
    apply Parallel_comm.
    econstructor.
    econstructor; eauto.
    eapply Parallel_assoc1.
    eassumption.
    eauto.

    (* IntMatch1 *)

    apply IHps in H3; clear IHps; firstorder; try congruence.

    inv H0.
    destruct a; simpl in *.
    destruct Code0; rewrite expand_proc0D in *; simpl in *.

    inv H1; eauto.
    do 3 right.
    inv H6.
    repeat esplit.
    eauto.
    eauto.
    eauto.
    econstructor.
    econstructor; eauto.
    eauto.
    eauto.

    inv H1.
    inv H1.

    do 3 right.
    repeat esplit.
    eapply perm_trans; [ | eapply perm_skip; eapply perm_swap ].
    eapply perm_trans; [ | eapply perm_swap ]; eauto.    
    eauto.
    eauto.
    simpl.
    apply Parallel_assoc2.
    apply Parallel_comm.
    apply Parallel_assoc1.
    eapply Parallel_cong.
    apply refines_refl.
    apply Parallel_comm.
    econstructor.
    econstructor; eauto.
    eapply Parallel_assoc1.
    eassumption.
    eauto.

    (* IntMatch2 *)

    apply IHps in H3; clear IHps; firstorder; try congruence.

    inv H0.
    destruct a; simpl in *.
    destruct Code0; rewrite expand_proc0D in *; simpl in *.

    inv H1; eauto.

    inversion H1; clear H1.
    destruct H8.
    destruct H10.
    apply (inj_pair2_eq_dec _ string_dec) in H7; subst.
    apply (inj_pair2_eq_dec _ string_dec) in H9; subst.
    do 3 right.
    inv H6.
    repeat esplit.
    eapply perm_trans; [ | apply perm_swap ].
    eauto.
    eauto.
    eauto.
    eapply Parallel_cong.
    apply refines_refl.
    apply Parallel_comm.
    apply Parallel_assoc2.
    econstructor.
    eauto.
    econstructor; eauto.
    eauto using interleave_sym.

    inv H1.

    do 3 right.
    repeat esplit.
    eapply perm_trans; [ | eapply perm_skip; eapply perm_swap ].
    eapply perm_trans; [ | eapply perm_swap ]; eauto.
    eauto.
    eauto.
    simpl.
    apply Parallel_assoc2.
    apply Parallel_comm.
    apply Parallel_assoc1.
    eapply Parallel_cong.
    apply refines_refl.
    apply Parallel_comm.
    econstructor.
    econstructor; eauto.
    eapply Parallel_assoc1.
    eassumption.
    eauto.
  Qed.

  Lemma whenStep : forall TP ps tr, traceOf (procsD {| TopChans := TP; Procs := ps |}) tr
    -> (* Trace ends *)
    tr = nil

    \/ (* Send *)
    (exists tr' P ch v k ps', Permutation ps ({| Chans := P; Code := NSend ch v k |} :: ps')
      /\ tr = (Send, existT _ ch v) :: tr'
      /\ TP (Send, ch)
      /\ P (Send, ch)
      /\ traceOf (procsD {| TopChans := TP;
                            Procs := {| Chans := P;
                                        Code := k |} :: ps' |}) tr')

    \/ (* Recv *)
    (exists tr' P ch v k ps', Permutation ps ({| Chans := P; Code := NRecv ch k |} :: ps')
      /\ tr = (Recv, existT _ ch v) :: tr'
      /\ TP (Recv, ch)
      /\ P (Recv, ch)
      /\ traceOf (procsD {| TopChans := TP;
                            Procs := {| Chans := P;
                                        Code := k v |} :: ps' |}) tr')

    \/ (* Rendezvous *)
    (exists P1 P2 ch v k1 k2 ps',
       Permutation ps ({| Chans := P1; Code := NSend ch v k1 |}
                         :: {| Chans := P2; Code := NRecv ch k2 |} :: ps')
       /\ P1 (Send, ch)
       /\ P2 (Recv, ch)
       /\ traceOf (procsD {| TopChans := TP;
                             Procs := {| Chans := P1;
                                         Code := k1 |}
                                        :: {| Chans := P2;
                                              Code := k2 v |}
                                        :: ps' |}) tr).
  Proof.
    intros.
    inv H; eauto.
    apply whenStep' in H2; firstorder.

    subst; inv H4.
    right; left.
    repeat esplit; eauto.
    econstructor; eauto.

    subst; inv H4.
    do 2 right; left.
    repeat esplit; eauto.
    econstructor; eauto.

    do 3 right.
    repeat esplit; eauto.
    econstructor; eauto.
  Qed.

  Lemma Permutation_traceOf' : forall ps1 ps2, Permutation ps1 ps2
    -> forall tr, traceOf (procsD' ps1) tr
      -> traceOf (procsD' ps2) tr.
  Proof.
    induction 1; simpl; intuition.

    inv H0; eauto.

    apply Parallel_assoc2.
    eapply Parallel_cong.
    apply Parallel_comm.
    apply refines_refl.
    apply Parallel_assoc1; auto.
  Qed.

  Theorem Permutation_traceOf : forall ps1 ps2, Permutation ps1 ps2
    -> forall P tr, traceOf (procsD {| TopChans := P; Procs := ps1 |}) tr
      -> traceOf (procsD {| TopChans := P; Procs := ps2 |}) tr.
  Proof.
    intros.
    inv H0; eauto.
    econstructor; eauto using Permutation_traceOf'.
  Qed.

  Lemma oneStep' : forall (TP1 TP2 : _ -> Prop) ps2 ps1,
    (forall P1 ch v k1 ps1', Permutation ps1 ({| Chans := P1; Code := NSend ch v k1 |} :: ps1')
       -> P1 (Send, ch)
       -> TP1 (Send, ch)
       -> exists P2 k2 ps2', Permutation ps2 ({| Chans := P2; Code := NSend ch v k2 |} :: ps2')
                             /\ P2 (Send, ch)
                             /\ TP2 (Send, ch)
                             /\ refines (procsD {| TopChans := TP1;
                                                   Procs := {| Chans := P1; Code := k1 |} :: ps1' |})
                                        (procsD {| TopChans := TP2;
                                                   Procs := {| Chans := P2; Code := k2 |} :: ps2' |}))
    -> (forall P1 ch k1 ps1', Permutation ps1 ({| Chans := P1; Code := NRecv ch k1 |} :: ps1')
       -> P1 (Recv, ch)
       -> TP1 (Recv, ch)
       -> exists P2 k2 ps2', Permutation ps2 ({| Chans := P2; Code := NRecv ch k2 |} :: ps2')
                             /\ P2 (Recv, ch)
                             /\ TP2 (Recv, ch)
                             /\ forall v, refines (procsD {| TopChans := TP1;
                                                             Procs := {| Chans := P1; Code := k1 v |} :: ps1' |})
                                                  (procsD {| TopChans := TP2;
                                                             Procs := {| Chans := P2; Code := k2 v |} :: ps2' |}))
    -> (forall P1 P2 ch v k1 k2 ps', Permutation ps1 ({| Chans := P1; Code := NSend ch v k1 |}
                                                     :: {| Chans := P2; Code := NRecv ch k2 |}
                                                     :: ps')
       -> P1 (Send, ch)
       -> P2 (Recv, ch)
       -> refines (procsD {| TopChans := TP1;
                             Procs := {| Chans := P1; Code := k1 |}
                                        :: {| Chans := P2; Code := k2 v |}
                                        :: ps' |})
                  (procsD {| TopChans := TP2; Procs := ps2 |}))
    -> refines (procsD {| TopChans := TP1; Procs := ps1 |}) (procsD {| TopChans := TP2; Procs := ps2 |}).
  Proof.
    intros; do 2 intro.
    apply whenStep in H2; firstorder; subst; eauto.

    specialize (H _ _ _ _ _ H2); firstorder.
    eapply Permutation_traceOf.
    apply Permutation_sym; eassumption.
    simpl.
    assert (traceOf (Restrict TP2 (procD {| Chans := x5; Code := x6 |} || procsD' x7)) x) by eauto.
    inv H9; eauto.
    inv H12; eauto.
    inv H11; eauto.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    apply interleave_nil1 in H16; subst.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.

    specialize (H0 _ _ _ _ H2); firstorder.
    eapply Permutation_traceOf.
    apply Permutation_sym; eassumption.
    assert (traceOf (Restrict TP1 (procD {| Chans := x0; Code := x3 x2 |} || procsD' x4)) x) by eauto.
    unfold procsD in *; simpl in *.
    apply H8 in H9.
    inv H9; eauto.
    inv H12; eauto.
    inv H11; eauto.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    apply interleave_nil1 in H16; subst.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.

    specialize (H1 _ _ _ _ _ _ _ H2); firstorder.
  Qed.

  (* Easier statement to work with *)

  Inductive pick1 {A : Type} : list A -> A -> list A -> Prop :=
  | Fst1 : forall x ls, pick1 (x :: ls) x ls
  | More1 : forall x y ls ls', pick1 ls y ls' -> pick1 (x :: ls) y (x :: ls').

  Hint Constructors pick1.

  Theorem pick1_Permutation : forall A (ls : list A) x ls',
    pick1 ls x ls'
    -> Permutation ls (x :: ls').
  Proof.
    induction 1; eauto.
    eapply perm_trans; [ | apply perm_swap ].
    eauto.
  Qed.

  Lemma Permutation_pick1' : forall A x (ls : list A) ls',
    Permutation ls ls'
    -> forall ls'', pick1 ls x ls''
      -> exists ls''', Permutation ls'' ls''' /\ pick1 ls' x ls'''.
  Proof.
    induction 1; intuition (subst; eauto); try congruence.

    inv H0; eauto.
    apply IHPermutation in H5; firstorder eauto.

    inv H; eauto.
    inv H4; eauto.
    do 2 esplit; [ | eauto ].
    apply perm_swap.

    apply IHPermutation1 in H1; firstorder.
    apply IHPermutation2 in H2; firstorder.
    do 2 esplit; [ | eauto ].
    eauto using perm_trans.
  Qed.

  Theorem Permutation_pick1 : forall A (ls : list A) x ls',
    Permutation ls (x :: ls')
    -> exists ls'', Permutation ls' ls'' /\ pick1 ls x ls''.
  Proof.
    intros.
    assert (pick1 (x :: ls') x ls') by auto.
    eapply Permutation_pick1' in H0.
    2: apply Permutation_sym; eassumption.
    eauto.
  Qed.

  Theorem oneStep : forall (TP1 TP2 : _ -> Prop) ps2 ps1,
    (forall P1 ch v k1 p ps1', pick1 ps1 p ps1'
       -> p = {| Chans := P1; Code := NSend ch v k1 |}
       -> P1 (Send, ch)
       -> TP1 (Send, ch)
       -> exists P2 k2 ps2', pick1 ps2 {| Chans := P2; Code := NSend ch v k2 |} ps2'
                             /\ P2 (Send, ch)
                             /\ TP2 (Send, ch)
                             /\ refines (procsD {| TopChans := TP1;
                                                   Procs := {| Chans := P1; Code := k1 |} :: ps1' |})
                                        (procsD {| TopChans := TP2;
                                                   Procs := {| Chans := P2; Code := k2 |} :: ps2' |}))
    -> (forall P1 ch k1 ps1', pick1 ps1 {| Chans := P1; Code := NRecv ch k1 |} ps1'
       -> P1 (Recv, ch)
       -> TP1 (Recv, ch)
       -> exists P2 k2 ps2', pick1 ps2 {| Chans := P2; Code := NRecv ch k2 |} ps2'
                             /\ P2 (Recv, ch)
                             /\ TP2 (Recv, ch)
                             /\ forall v, refines (procsD {| TopChans := TP1;
                                                             Procs := {| Chans := P1; Code := k1 v |} :: ps1' |})
                                                  (procsD {| TopChans := TP2;
                                                             Procs := {| Chans := P2; Code := k2 v |} :: ps2' |}))
    -> (forall P1 P2 ch v k1 k2 ps'' ps', pick1 ps1 {| Chans := P1; Code := NSend ch v k1 |} ps'
       -> pick1 ps' {| Chans := P2; Code := NRecv ch k2 |} ps''
       -> P1 (Send, ch)
       -> P2 (Recv, ch)
       -> refines (procsD {| TopChans := TP1;
                             Procs := {| Chans := P1; Code := k1 |}
                                        :: {| Chans := P2; Code := k2 v |}
                                        :: ps'' |})
                  (procsD {| TopChans := TP2; Procs := ps2 |}))
    -> refines (procsD {| TopChans := TP1; Procs := ps1 |})
               (procsD {| TopChans := TP2; Procs := ps2 |}).
  Proof.
    intros; eapply oneStep'; eauto; intros.

    apply Permutation_pick1 in H2; firstorder.
    specialize (H P1 _ v k1 _ _ H5); firstorder.
    repeat esplit.
    eauto using pick1_Permutation.
    eauto.
    eauto.
    do 2 intro.
    apply H8.
    inv H9; eauto.
    inv H12; eauto.
    econstructor.
    econstructor.
    eauto.
    eapply Permutation_traceOf'.
    eassumption.
    eauto.
    auto.
    eauto.

    apply Permutation_pick1 in H2; firstorder.
    specialize (H0 _ _ _ _ H5); firstorder.
    repeat esplit.
    eauto using pick1_Permutation.
    eauto.
    eauto.
    do 3 intro.
    apply H8.
    inv H9; eauto.
    inv H12; eauto.
    econstructor.
    econstructor.
    eauto.
    eapply Permutation_traceOf'.
    eassumption.
    eauto.
    auto.
    eauto.

    apply Permutation_pick1 in H2.
    destruct H2; intuition.
    apply Permutation_sym in H5.
    apply Permutation_pick1 in H5.
    destruct H5; intuition.
    specialize (H1 _ _ _ _ _ _ _ _ H6 H7); intuition.
    do 2 intro.
    apply H1.
    inv H2; eauto.
    inv H10; eauto.
    inv H11; eauto.
    econstructor.
    eauto.
    econstructor.
    eauto.
    econstructor.
    eauto.
    eapply Permutation_traceOf'.
    eassumption.
    eauto.
    eauto.
    eauto.
    eauto.
    apply interleave_nil2 in H14; subst.
    econstructor.
    simpl.
    econstructor.
    eauto.
    econstructor.
    eauto.
    eapply Permutation_traceOf'.
    eassumption.
    eauto.
    eauto.
    eauto.
    eauto.
  Qed.


  (** * Filtering out inert processes *)

  Inductive filterInert : process chs -> process chs -> Prop :=
  | FiParallel : forall p1 ps1 p2 ps2, filterInert p1 ps1
    -> filterInert p2 ps2
    -> filterInert (p1 || p2) (match ps1 with
                               | Done => ps2
                               | _ => match ps2 with
                                      | Done => ps1
                                      | _ => ps1 || ps2
                                      end
                               end)
  | FiRestrictTrue : forall p ps, filterInert p ps
    -> filterInert (Restrict (fun _ => True) p) ps
  | FiRestrict : forall P p ps, filterInert p ps
    -> filterInert (Restrict P p) (Restrict P ps)
  | FiOther : forall p, filterInert p p.

  Theorem filterInert_fwd : forall p ps, filterInert p ps
    -> forall tr, traceOf p tr
      -> traceOf ps tr.
  Proof.
    induction 1; intuition eauto.

    inv H1; eauto.
    destruct ps1, ps2; eauto;
      match goal with
      | [ H : forall tr : trace chs, _, H' : _ |- _ ] => apply H in H'; inv H';
                                                         match goal with
                                                         | [ H : _ |- _ ] =>
                                                           (apply interleave_nil1 in H
                                                            || apply interleave_nil2 in H);
                                                             subst; solve [ eauto ]
                                                         end
      end.

    inv H0; eauto.

    inv H0; eauto.
  Qed.

  Theorem filterInert_bwd : forall p ps, filterInert p ps
    -> forall tr, traceOf ps tr
      -> traceOf p tr.
  Proof.
    induction 1; intuition eauto.

    destruct ps1, ps2; inv H1; eauto;
    match goal with
    | [ H : forall tr : trace chs, _ |- _ ] =>
      solve [ econstructor; try (apply H; econstructor; eauto); eauto ]
    end.

    inv H0; eauto.
  Qed.

  Theorem refines_filterInert : forall p1 p2 ps1 ps2,
    filterInert p1 ps1
    -> filterInert p2 ps2
    -> refines ps1 ps2
    -> refines p1 p2.
  Proof.
    unfold refines; eauto using filterInert_fwd, filterInert_bwd.
  Qed.


  (** * Running internal computation steps on the RHS of [refines] *)

  Theorem compute_rhs : forall p TP ps ch v k1 k2 P1 P2 ps' ps'',
    pick1 ps {| Chans := P1; Code := NSend ch v k1 |} ps'
    -> pick1 ps' {| Chans := P2; Code := NRecv ch k2 |} ps''
    -> P1 (Send, ch)
    -> P2 (Recv, ch)
    -> refines p (procsD {| TopChans := TP; Procs := {| Chans := P1; Code := k1 |}
                                                       :: {| Chans := P2; Code := k2 v |}
                                                       :: ps'' |})
    -> refines p (procsD {| TopChans := TP; Procs := ps |}).
  Proof.
    unfold refines; intros.
    apply H3 in H4; clear H3.
    inv H4; eauto.
    inv H6; eauto.
    inv H5; eauto.
    inv H7; eauto.
    inv H5; eauto.

    econstructor; simpl; auto.
    eapply Permutation_traceOf'.
    eapply pick1_Permutation in H.
    eapply Permutation_sym; eassumption.
    simpl.
    eapply Parallel_cong; [ apply refines_refl | | ].
    do 2 intro.
    eapply Permutation_traceOf'.
    eapply pick1_Permutation in H0.
    eapply Permutation_sym; eassumption.
    eassumption.
    simpl.
    apply Parallel_assoc2.
    destruct (interleave_reassoc1 _ _ _ H10 _ _ H13); intuition.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor; eauto.
    eauto.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor; eauto.
    eauto.
    eauto.
    eauto.
    eauto.

    apply interleave_nil1 in H13; subst.
    econstructor; simpl; auto.
    eapply Permutation_traceOf'.
    eapply pick1_Permutation in H.
    eapply Permutation_sym; eassumption.
    simpl.
    eapply Parallel_cong; [ apply refines_refl | | ].
    do 2 intro.
    eapply Permutation_traceOf'.
    eapply pick1_Permutation in H0.
    eapply Permutation_sym; eassumption.
    eassumption.
    simpl.
    apply Parallel_assoc2.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor; eauto.
    eauto.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor; eauto.
    eauto.
    eauto.
    eauto.
    eauto.

    apply interleave_nil2 in H10; subst.
    econstructor; simpl; auto.
    eapply Permutation_traceOf'.
    eapply pick1_Permutation in H.
    eapply Permutation_sym; eassumption.
    simpl.
    eapply Parallel_cong; [ apply refines_refl | | ].
    do 2 intro.
    eapply Permutation_traceOf'.
    eapply pick1_Permutation in H0.
    eapply Permutation_sym; eassumption.
    eassumption.
    simpl.
    apply Parallel_assoc2.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor; eauto.
    eauto.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor; eauto.
    eauto.
    eauto.
    eauto.
    eauto.

    apply interleave_nil1 in H10; subst.
    econstructor; simpl; auto.
    eapply Permutation_traceOf'.
    eapply pick1_Permutation in H.
    eapply Permutation_sym; eassumption.
    simpl.
    eapply Parallel_cong; [ apply refines_refl | | ].
    do 2 intro.
    eapply Permutation_traceOf'.
    eapply pick1_Permutation in H0.
    eapply Permutation_sym; eassumption.
    eassumption.
    simpl.
    apply Parallel_assoc2.
    inv H7; eauto.
    inv H5; eauto.
    econstructor.
    econstructor.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor.
    apply TrDone.
    eauto.
    econstructor.
    rewrite expand_proc0D; simpl.
    econstructor; eauto.
    eauto.
    eauto.
    eauto.
    eauto.
  Qed.

End Refinement.
