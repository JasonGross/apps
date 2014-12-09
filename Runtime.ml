type 'world action = 'world -> 'world;;

module type APPLICATION =
  sig

    type httpStatus =
      | HttpOk
      | HttpPreconditionFailed
      | HttpUnrecognizedCode

    type httpResponse = {
        httpResponseStatus : httpStatus;
        httpResponseStatusText : char list;
        httpResponseProtocol : char list;
        httpResponseHeader : (char list * char list) list;
        httpResponseBody : char list
      }

    type ('input, 'world) systemActions = {
        consoleOut : (char list -> 'world action);
        getNanosecs : (Big.big_int -> 'input) -> 'world action;
        getRandomness : Big.big_int -> (char list -> 'input) -> 'world action;
        httpPOST : (char list -> (char list * char list) list -> (httpResponse -> 'input) -> 'world action);
        sleepNanosecs : Big.big_int -> 'input -> 'world action;
      }

    type ('input, 'world) process = ('input, 'world) __process Lazy.t
    and ('input, 'world) __process =
      | Step of ('input -> 'world action * ('input, 'world) process)

    type input

    val proc : (input, 'world) systemActions -> (input, 'world) process

    val consoleIn : char list -> input

  end;;

module type MAIN =
  sig
    val main : unit -> unit
  end;;

Ssl.init ();;

Http_client.Debug.enable := true;;

let esys = Unixqueue.standard_event_system ();;

let stdin_buf = Uq_io.create_in_buffer (`Polldescr (`Read_write, Unix.stdin, esys));;

let urandom_buf =
  let fd = Unix.openfile "/dev/urandom" [Unix.O_RDONLY] 0 in
  Uq_io.create_in_buffer (`Polldescr (`Read_write, fd, esys));;

let pipeline = new Http_client.pipeline;;

let ctx = Ssl.create_context Ssl.TLSv1_2 Ssl.Client_context in
let tct = Https_client.https_transport_channel_type ctx in
pipeline # configure_transport Http_client.https_cb_id tct;;

pipeline # set_options { pipeline # get_options with
                         Http_client.verbose_connection = false;
                         Http_client.verbose_request_contents = true;
                         Http_client.verbose_response_contents = true; };;

pipeline # set_event_system esys;;

let getNanosecs () : Big_int.big_int =
  let (t, n) = Netsys_posix.clock_gettime Netsys_posix.CLOCK_MONOTONIC in
  Big_int.add_big_int
    (Big_int.mult_big_int
       (Big_int.big_int_of_int64 (Int64.of_float t))
       (Big_int.big_int_of_int 1000000000))
    (Big_int.big_int_of_int n);;

module Main(P : APPLICATION) : MAIN = struct
  let getStep proc =
    match Lazy.force proc with
    | P.Step f -> f

  let rec sys : (P.input, 'a) P.systemActions = {

    P.consoleOut = begin fun s () ->
      print_endline (ExtString.String.implode s)
    end;

    P.getNanosecs = begin fun cb () ->
      doStep (!step (cb (getNanosecs ())))
    end;

    P.getRandomness = begin fun len cb () ->
      let len' = Big_int.int_of_big_int len in
      let buf = String.create len' in
      let e = Uq_io.really_input_e (`Buffer_in urandom_buf) (`String buf) 0 len' in
      Uq_engines.when_state
        ~is_done:(fun () ->
          doStep (!step (cb (ExtString.String.explode buf))))
        ~is_error:(fun ex ->
          prerr_endline ("urandom: " ^ Printexc.to_string ex))
        e
    end;

    P.httpPOST = begin fun uri data cb () ->
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
    end;

    P.sleepNanosecs = begin fun t i () ->
      Unixqueue.once esys
        (Unixqueue.new_group esys)
        (Big_int.float_of_big_int t *. 1e-9)
        (fun () ->
          doStep (!step i))
    end;

  }
  and step = ref (fun i -> getStep (P.proc sys) i)
  and doStep (out, proc') =
    out ();
    step := getStep proc'

  let rec readStdin () =
    let e = Uq_io.input_line_e (`Buffer_in stdin_buf) in
    Uq_engines.when_state
      ~is_done:(fun s ->
        doStep (!step (P.consoleIn (ExtString.String.explode s)));
        readStdin ())
      ~is_error:(fun ex ->
        prerr_endline ("stdin: " ^ Printexc.to_string ex))
      e;
    ()

  let main () =
    readStdin ();
    Unixqueue.run esys
end;;
