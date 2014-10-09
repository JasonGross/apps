module P = ExamplePwMgr;;

let rec loop proc =
  match Lazy.force proc with
  | P.Step f ->
      match (Str.bounded_split (Str.regexp " ") (read_line ()) 2) with
      | ">" :: s :: nil ->
          loop' (f (P.UiConsoleIn (ExtString.String.explode s)))
      | "decrypted" :: s :: nil ->
          Scanf.sscanf s "%S" (fun data ->
            loop' (f (P.UiDecrypted (ExtString.String.explode data))))
      | _ ->
          prerr_endline "unrecognized input";
          loop proc
and loop' (outs, proc) =
  List.iter
    (fun o -> match o with
    | P.UiConsoleOut s -> print_endline ("< " ^ ExtString.String.implode s)
    | P.UiEncrypt s -> Printf.printf "encrypt %S\n%!" (ExtString.String.implode s))
    outs;
  loop proc;;

loop P.ui;;