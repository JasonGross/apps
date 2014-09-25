Set Implicit Arguments.
Require Import Arith Process Refinement ModelCheck.

(* Pi-calculus *)
CoInductive process :=
| DoSend (ch : channel) T (v : T) (k : process)
| DoRecv (ch : channel) T (k : T -> process)
| Parallel (pr1 pr2 : process)
| CreateChannel (k : channel -> process)
| RepeatedSpawn (pr : process)
| Restrict (which : direction * channel -> Prop) (k : process)
| Done.

Require Import List.
Notation "#! [ ch , v ] , k" := (DoSend ch v k) (at level 100).
Notation "#? [ ch , x ] , k" := (DoRecv ch (fun x => k)) (at level 100).
Notation "## [ x1 , .. , xN ] , k" := (Restrict (fun p => In p (cons x1 (.. (cons xN nil) ..))) k) (at level 100).
Infix "||" := Parallel.
Notation "#*, p" := (RepeatedSpawn p) (at level 100).
Notation "#@ ch , k" := (CreateChannel (fun ch => k)) (at level 100).

Fixpoint CreateChannels n (f : list channel -> process) : process :=
  match n with
    | 0 => f nil
    | S n'=> CreateChannels n' (fun chs => #@ch, f (ch :: chs))
  end.

Notation "#@* [ n , chs ] , k" := (CreateChannels n (fun chs => k)) (at level 100).

