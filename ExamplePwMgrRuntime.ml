module P = ExamplePwMgr;;

let rec loop proc =
  match Lazy.force proc with
  | P.Step f ->
      match (Str.bounded_split (Str.regexp " ") (read_line ()) 2) with
      | ">" :: s :: nil ->
          loop' (f (P.PwMgrConsoleIn (ExtString.String.explode s)))
      | "received" :: s :: nil ->
          Scanf.sscanf s "%S" (fun data ->
            loop' (f (P.PwMgrReceived (ExtString.String.explode data))))
      | _ ->
          prerr_endline "unrecognized input";
          loop proc
and loop' (out, proc) =
  out ();
  loop proc;;

let pwMgrConsoleOut s () =
  print_endline ("< " ^ ExtString.String.implode s);;

let pwMgrSend s () =
  Printf.printf "send %S\n%!" (ExtString.String.implode s);;

let proc = P.pwMgr pwMgrConsoleOut pwMgrSend;;

loop proc
