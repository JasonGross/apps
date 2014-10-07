Require Import List.
Import ListNotations.

Section process.
  Context {input output: Type}.

  CoInductive process :=
  | Step : (input -> list output * process) -> process.
End process.

Arguments process : clear implicits.

Require Import Ascii.

Definition game : process ascii (nat * nat * bool) :=
  (cofix loop n := Step (fun _ => ([(n, n, true)], loop (n + 1)))) 0.
