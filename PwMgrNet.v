Require Import FunctionApp List String System.
Import ListNotations.
Open Scope string_scope.

Section net.

  Inductive netInput :=
  | netGetUpdate
  | netCAS (old new : string)
  | netSendGotUpdate (new : string)
  | netHttpError (r : httpResponse).

  Context (world : Type).

  Inductive netOutput :=
  | netGotUpdate (new : string)
  | netHttpPOST (uri : string) (data : list (string * string)) (cb : httpResponse -> netInput).

  Context (send : netOutput -> action world).
  Context (storageId : string).

  Definition storageURI := "https://andersk.scripts.mit.edu/pwmgr/storage".

  Definition storageGet id cb :=
    send (netHttpPOST
            (storageURI ++ "/get") [("id", id)]
            (fun r => match httpResponseStatus r with
                        | httpOk => cb (httpResponseBody r)
                        | _ => netHttpError r
                      end)).
  Definition storageSet id old new cb :=
    send (netHttpPOST
            (storageURI ++ "/set") [("id", id); ("old", old); ("new", new)]
            (fun r => match httpResponseStatus r with
                        | httpOk => cb None  (* compare-and-set succeeded *)
                        | httpPreconditionFailed => cb (Some (httpResponseBody r))  (* remote value differed *)
                        | _ => netHttpError r
                      end)).
  Definition storagePoll id old cb :=
    send (netHttpPOST
            (storageURI ++ "/poll") [("id", id); ("old", old)]
            (fun r => match httpResponseStatus r with
                        | httpOk => cb (httpResponseBody r)
                        | _ => netHttpError r
                      end)).

  CoFixpoint net :=
    Step (fun i =>
            match i with
              | netGetUpdate =>
                (storageGet
                   storageId
                   (fun new => netSendGotUpdate new),
                net)
              | netCAS old new =>
                (storageSet
                   storageId old new
                   (fun ret => netSendGotUpdate
                                 match ret with
                                   | None => new
                                   | Some other => other
                                 end),
                 net)
              | netSendGotUpdate new => (send (netGotUpdate new), net)
              | netHttpError _ => (id, net)
            end).

End net.
