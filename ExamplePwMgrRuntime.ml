Ssl.init ();;

Http_client.Debug.enable := true;;

let esys = Unixqueue.standard_event_system ();;

let stdin_buf = Uq_io.create_in_buffer (`Polldescr (`Read_write, Unix.stdin, esys));;

let pipeline = new Http_client.pipeline;;

let ctx = Ssl.create_context Ssl.TLSv1_2 Ssl.Client_context in
let tct = Https_client.https_transport_channel_type ctx in
pipeline # configure_transport Http_client.https_cb_id tct;;

pipeline # set_options { pipeline # get_options with
                         Http_client.verbose_connection = false;
                         Http_client.verbose_request_contents = true;
                         Http_client.verbose_response_contents = true; };;

pipeline # set_event_system esys;;

module P = ExamplePwMgr;;

let getStep proc =
  match Lazy.force proc with
  | P.Step f -> f;;

let pwMgrConsoleOut s () =
  print_endline (ExtString.String.implode s)

let rec pwMgrHttpPost uri data cb () =
  let r = new Http_client.post (ExtString.String.implode uri) (List.map (fun (k, v) -> (ExtString.String.implode k, ExtString.String.implode v)) data) in
  pipeline # add_with_callback r (fun m ->
    match m # status with
    | `Successful | `Redirection | `Client_error | `Server_error ->
        let status = match m # response_status with
        | `Ok -> P.HttpOk
        | `Precondition_failed -> P.HttpPreconditionFailed
        | _ -> P.HttpUnrecognizedCode in
        let i = cb {
          P.httpResponseStatus = status;
          P.httpResponseStatusText = ExtString.String.explode (m # response_status_text);
          P.httpResponseProtocol = ExtString.String.explode (m # response_protocol);
          P.httpResponseHeader = List.map (fun (k, v) -> (ExtString.String.explode k, ExtString.String.explode v)) (m # response_header # fields);
          P.httpResponseBody = ExtString.String.explode (m # response_body # value) } in
        doStep (!step i)
    | `Http_protocol_error ex -> prerr_endline ("HTTP: " ^ Printexc.to_string ex)
    | `Unserved -> prerr_endline "HTTP: unserved request")
and step = ref (fun i -> getStep (P.pwMgr pwMgrConsoleOut pwMgrHttpPost) i)
and doStep (out, proc') =
  out ();
  step := getStep proc';;

let rec loop () =
  let e = Uq_io.input_line_e (`Buffer_in stdin_buf) in
  Uq_engines.when_state
    ~is_done:(fun s ->
      doStep (!step (P.PwMgrConsoleIn (ExtString.String.explode s)));
      loop ())
    ~is_error:(fun ex ->
      prerr_endline ("stdin: " ^ Printexc.to_string ex))
    e;
  () in
loop ();;

Unixqueue.run esys;;
