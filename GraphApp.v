Section hlist.
  (* Heterogeneous lists and variants. *)

  Context {a : Type} {b : a -> Type}.

  Inductive hlist : list a -> Type :=
  | HNil : hlist nil
  | HCons {x : a} {ls : list a} : b x -> hlist ls -> hlist (x :: ls).

  Definition huncons {x xs} (h : hlist (x :: xs)) :=
    let 'HCons _ _ y h' := h in (y, h').

  Inductive hsum : list a -> Type :=
  | HHead {x : a} {ls : list a} : b x -> hsum (x :: ls)
  | HTail {x : a} {ls : list a} : hsum ls -> hsum (x :: ls).
End hlist.

Arguments hlist {a} b _.
Arguments hsum {a} b _.


Section process.
  (* A process reads from one input channel and writes to one output
  channel. *)

  Context {input output : Type}.

  CoInductive process :=
  | DoRecv : (input -> process) -> process
  | DoSend : output -> process -> process.

  (* mapProc f generates one output for each input. *)
  CoFixpoint mapProc f :=
    DoRecv (fun x => DoSend (f x) (mapProc f)).
End process.

Arguments process : default implicits.


Section network.
  (* PHOAS-like graph representation. *)

  Context {var : Type -> Type}.

  Inductive network : Type -> Type :=
  | Var {input} : var input -> network input
  | Mu {inputs input} :
      (hlist var inputs -> hlist network inputs * network input) ->
      network input
  | Node {input outputs} :
      process input (hsum (@id _) outputs) ->
      hlist network outputs ->
      network input.

  (* Convenience wrappers because destructuring hlist sucks. *)
  Definition Mu1 {input0 input}
             (f : var input0 ->
                  network input0 * network input) :=
    Mu (fun vars =>
          let (v0, _) := huncons vars in
          let (n0, n) := f v0 in
          (HCons n0 HNil, n)).
  Definition Mu2 {input0 input1 input}
             (f : var input0 -> var input1 ->
                  network input0 * network input1 * network input) :=
    Mu (fun vars =>
          let (v0, vars1) := huncons vars in
          let (v1, _) := huncons vars1 in
          let '(n0, n1, n) := f v0 v1 in
          (HCons n0 (HCons n1 HNil), n)).
  Definition Mu3 {input0 input1 input2 input}
             (f : var input0 -> var input1 -> var input2 ->
                  network input0 * network input1 * network input2 * network input) :=
    Mu (fun vars =>
          let (v0, vars1) := huncons vars in
          let (v1, vars2) := huncons vars1 in
          let (v2, _) := huncons vars2 in
          let '(n0, n1, n2, n) := f v0 v1 v2 in
          (HCons n0 (HCons n1 (HCons n2 HNil)), n)).
End network.

Arguments network : default implicits.


(* Ping-pong example. *)
Definition pingpong var t : network var t :=
  Mu2 (fun a b =>
         (Node (mapProc HHead) (HCons (Var b) HNil),
          Node (mapProc HHead) (HCons (Var a) HNil),
          Var a)).
