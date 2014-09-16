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

Require Import String List.
Notation "#! [ ch , v ] , k" := (DoSend ch v k) (at level 100).
Notation "#? [ ch , x ] , k" := (DoRecv ch (fun x => k)) (at level 100).
Notation "## [ x1 , .. , xN ] , k" := (Restrict (fun p => In p (cons x1 (.. (cons xN nil) ..))) k) (at level 100).
Infix "||" := Parallel.
Notation "#*, p" := (RepeatedSpawn p) (at level 100).
Notation "#@ ch , k" := (CreateChannel (fun ch => k)) (at level 100).
Import ListNotations.

(* An example adapted from OKWS, a web server with privilege separation 
   Reference paper: 
   Maxwell Krohn, Building Secure High-Performance Web Services with OKWS *)

Definition HTTP_PORT := "80".

Definition HTTP_404 (sock : channel) := #![sock, "Response 404"], Done.

Definition Dispatcher := string -> option channel.

(* The dispatching deamon, which listens to port 80 and dispatches incoming HTTP requests according to the first line of the request *)
Definition okd (dispatcher : Dispatcher) :=
  #*, #?[HTTP_PORT, sock], #?[sock, reqpath], 
  match dispatcher reqpath with
    | Some svc => #![svc, reqpath], #![svc, sock], Done
    | None => HTTP_404 sock
  end.

Definition Service := string -> channel -> process.

(* The launcher, which launches okd and a collection of services, and sets up dispatching rules *)
Section okld.

  Variable make_dispatcher : list (string * channel) -> Dispatcher.

  (* A helper *)
  Definition start_svc (svc : Service) ch := #?[ch, reqpath], #?[ch, sock], svc reqpath sock.

  (* An example launcher for a fixed number of services *)
  Definition okld3 ptrn1 svc1 ptrn2 svc2 ptrn3 svc3 :=
    #@ch1, #@ch2, #@ch3,
    let dispatcher := make_dispatcher [(ptrn1, ch1); (ptrn2, ch2); (ptrn3, ch3)] in
    okd dispatcher ||
    start_svc svc1 ch1 ||
    start_svc svc2 ch2 ||
    start_svc svc3 ch3.

  Fixpoint CreateChannels n (f : list channel -> process) : process :=
    match n with
      | 0 => f []
      | S n'=> CreateChannels n' (fun chs => #@ch, f (ch :: chs))
    end.

  Notation "#@* [ n , chs ] , k" := (CreateChannels n (fun chs => k)) (at level 100).

  Definition fold_left2 A B C (f : A -> B -> C -> A) ls1 ls2 a := fold_left (fun a x => f a (fst x) (snd x)) (combine ls1 ls2) a.

  (* A more general launcher for an arbitrary list of services *)
  Definition okld (svcs : list (string * Service)) := 
    #@*[length svcs, chans],
    let (patterns, svcs) := split svcs in
    let dispatcher := make_dispatcher (combine patterns chans) in
    fold_left2 (fun pr ch svc => pr || start_svc svc ch) chans svcs (okd dispatcher).

End okld.