Inductive sum' : list Type -> Type :=
| SHead {t ts} : t -> sum' (t :: ts)
| STail {t ts} : sum' ts -> sum' (t :: ts).


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

  Inductive network : list Type -> Type :=
  | Empty : network nil
  | Var {input} :
      var input ->
      forall {inputs}, network inputs -> network (input :: inputs)
  | Mu {input inputs} :
      (var input -> network (input :: inputs)) -> network inputs
  | Node {input outputs} :
      process input (sum' outputs) ->
      network outputs ->
      forall {inputs}, network inputs -> network (input :: inputs).
End network.

Arguments network : default implicits.


(* Ping-pong example. *)
Definition pingpong var t : network var (t :: nil) :=
  Mu (fun a =>
        Mu (fun b =>
              Node (mapProc SHead) (Var a Empty)
                   (Node (mapProc SHead) (Var b Empty)
                         (Var a Empty)))).
