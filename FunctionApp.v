Section process.
  Context {input output: Type}.

  CoInductive process :=
  | Step : (input -> list output * process) -> process.
End process.

Arguments process : clear implicits.
