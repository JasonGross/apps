Require Import Process Refinement List Eqdep_dec.


Ltac normBasic' E :=
  match eval simpl in E with
  | fun x : ?A => @Done ?chs =>
    constr:(fun x : A => @NDone chs)
  | fun x : ?A => @DoSend ?chs ?ch (@?v x) (@?k x) =>
    let E' := normBasic' k
      in constr:(fun x : A => @NSend chs ch (v x) (E' x))
  | fun x : ?A => @DoRecv ?chs ?ch (@?k x) =>
    let E' := normBasic' (fun p : A * _ => k (fst p) (snd p))
      in constr:(fun x : A => @NRecv chs ch (fun y => E' (x, y)))
  | fun x : ?A => if @?test x then @?case1 x else @?case2 x =>
    let E1 := normBasic' case1 in
    let E2 := normBasic' case2 in
      constr:(fun x : A => if test x then E1 x else E2 x)
  end.

Ltac normBasic0 E :=
  let E := eval hnf in E in
  let E' := normBasic' (fun _ : unit => E) in
    eval simpl in (E' tt).

Ltac normBasic :=
  match goal with
  | [ |- normalize _ ?E ?F ] =>
    let E' := normBasic0 E in unify F E'
  end.

Ltac normalize := solve [ repeat (solve [ apply normProcD | apply normProc0D
                                        | eapply normBasic;
                                          normBasic; repeat (constructor; intros) ]
                       || eapply normParallel || eapply normRestrictTrivial
                       || eapply normRestrictMany) ].

Ltac inverter H := let H' := fresh "H'" in
                   generalize H; intro H'; apply (f_equal (@Chans _)) in H'; simpl in H'; subst;
                   apply (f_equal (@Code _)) in H; simpl in H; subst.

Definition channelOf {chs} (p : proc0 chs) :=
  match p with
  | NSend ch _ _ => ch
  | NRecv ch _ => ch
  | NDone => ""
  end.

Inductive simplified {chs} (ch : string) : Type :=
| SSend (v : chs ch) (k : proc0 chs)
| SRecv (k : chs ch -> proc0 chs)
| SDone.

Definition simplify {chs} (p : proc0 chs) : simplified (channelOf p) :=
  match p with
  | NSend _ v k => SSend _ v k
  | NRecv _ k => SRecv _ k
  | NDone => SDone _
  end.

Require Import Eqdep_dec.

Ltac inverter2 H := let H' := fresh "H'" in generalize H; intro H';
                    apply (f_equal (@channelOf _)) in H'; simpl in H'; subst;
                    apply (f_equal (fun x => existT simplified (channelOf x) (simplify x))) in H;
                    simpl in H; apply (inj_pair2_eq_dec _ string_dec) in H; inv H.

Ltac oneStep0 :=
  match goal with
  | _ => discriminate
  | [ H : _ :: _ = _ :: _ |- _ ] => inv H
  | [ H : pick1 ?ls _ _ |- _ ] => remember ls; inv H

  | [ H : Build_proc _ _ _ = Build_proc _ _ _ |- _ ] => inverter H
  | [ H : NSend _ _ _ _ = NSend _ _ _ _ |- _ ] => inverter2 H
  | [ H : NRecv _ _ _ = NRecv _ _ _ |- _ ] => inverter2 H
  end.

Ltac oneStep' := simpl; intros; repeat oneStep0.

Ltac oneStep :=
  apply oneStep; oneStep'.

Ltac picker' ls toHere k :=
  match ls with
  | _ :: ?ls' =>
    k ltac:(toHere; apply Fst1)
    || picker' ls' ltac:(toHere; apply More1) k
  end.

Ltac picker :=
  match goal with
  | [ |- exists P k ps', pick1 ?ls _ _ /\ P _ /\ _ ] =>
    picker' ls idtac ltac:(fun tac => do 4 esplit; [ tac | split; [ simpl; tauto | intros ] ])
  end.

Ltac filter := eapply refines_filterInert; [ solve [ repeat constructor ]
                                           | solve [ repeat constructor ]
                                           | cbv beta; simpl ].

Ltac simper := intuition;
  repeat match goal with
         | [ H : True |- _ ] => clear H
         | [ H : (?X, ?Y) = (?X, ?Y) |- _ ] => clear H
         end; unfold procsD; simpl; try discriminate; try filter.

Ltac refines := eapply refines_normalize; [ normalize | normalize | oneStep; try picker ];
                simper.
