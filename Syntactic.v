Require Import String.

Set Implicit Arguments.

Section handler.
  Variable methods : Type -> Type.
  Variable state : Type.

  Inductive handler :=
  | Done
  | MethodCall dom (m : methods dom) (arg : dom) (k : handler)
  | Read (k : state -> handler)
  | Write (st : state) (k : handler).
End handler.

Arguments Done {methods state}.

Section program.
  Variable node : Type.
  Variable signatureOf : node -> string -> Type.

  Record implementation (n : node) := {
    State : Type;
    InitialState : State;
    Methods : forall (s : string), signatureOf n s
                                   -> handler (fun T => {n : node & { s : string | signatureOf n s = T } }) State
  }.

  Inductive nodeImpl (n : node) :=
  | External
  | Internal (impl : implementation n).

  Definition implementations := forall n, nodeImpl n.
End program.

Arguments External {node signatureOf n}.

Open Scope string_scope.

Module Echoer.
  Inductive node := World | Echoer.

  Definition signatureOf (n : node) (_ : string) : Type :=
    match n with
      | World => nat * nat
      | Echoer => nat
    end%type.

  Definition impls : implementations signatureOf :=
    fun n => match n with
               | World => External
               | Echoer => Internal
                             (Build_implementation
                                signatureOf
                                Echoer
                                tt
                                (fun _ n => MethodCall (existT _ World (exist _ "foo" eq_refl)) (n, n)
                                                       (Write tt Done)))
             end.
End Echoer.
