Require Import FunctionApp String.

Inductive httpStatus :=
| httpOk
| httpPreconditionFailed
| httpUnrecognizedCode.

Record httpResponse :=
  {
    httpResponseStatus : httpStatus;
    httpResponseStatusText : string;
    httpResponseProtocol : string;
    httpResponseHeader : list (string * string);
    httpResponseBody : string
  }.

Section systemActions.
  Context {input : Type}.
  Context {world : Type}.
  Record systemActions :=
    {
      consoleOut : string -> action world;
      httpPOST : string -> list (string * string) -> (httpResponse -> input) -> action world
    }.
End systemActions.

Arguments systemActions : clear implicits.
