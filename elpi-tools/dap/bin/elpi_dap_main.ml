(* elpi-dap: a debug adapter for Elpi programs.

   It speaks the Debug Adapter Protocol on stdin and stdout (VS Code
   starts it), runs elpi-debug -machine on the program and the goal of
   the launch request, and translates (see ../lib/session.ml and
   ../README.md).  One loop waits on the client and on elpi-debug, and
   hands each complete message to the session. *)

open Elpi_dap

let client = Wire.input Unix.stdin

(* [write_to_client json]: a message on stdout, with its DAP header. *)
let write_to_client json = Wire.write_all Unix.stdout (Wire.frame (Yojson.Safe.to_string json))

(* [read_client session]: the complete requests that arrived. *)
let rec read_client session =
  match Wire.next_message client with
  | Some body ->
      (match Protocol.request_of_string body with
       | r -> Session.on_request session r
       | exception Protocol.Not_a_request msg -> prerr_endline ("elpi-dap: not a request: " ^ msg));
      read_client session
  | None -> ()

(* [read_debuggee session input which]: the complete lines of elpi-debug
   on its stdout or stderr. *)
let rec read_debuggee session input which =
  match Wire.next_line input with
  | Some line ->
      (match which with
       | `Output -> Session.on_debuggee_line session line
       | `Errors -> Session.on_debuggee_error_line session line);
      read_debuggee session input which
  | None -> ()

(* [wait_for_input inputs]: the inputs that have data (or reached their
   end), waiting for at least one. *)
let wait_for_input inputs =
  let open_inputs = List.filter (fun (i : Wire.input) -> not i.closed) inputs in
  let fds = List.map (fun (i : Wire.input) -> i.fd) open_inputs in
  match Unix.select fds [] [] (-1.0) with
  | ready, _, _ -> List.filter (fun (i : Wire.input) -> List.mem i.fd ready) open_inputs
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> []

let rec loop session =
  let debuggee = Session.debuggee_inputs session in
  let ready = wait_for_input (client :: List.map fst debuggee) in
  List.iter
    (fun (i : Wire.input) ->
      Wire.fill i;
      if i == client then read_client session
      else read_debuggee session i (List.assq i debuggee))
    ready;
  (match session.Session.debuggee with
   | Some d when Debuggee.ended d -> Session.on_debuggee_end session
   | _ -> ());
  if not (session.Session.finished || client.closed) then loop session

let () =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let session = Session.create ~write:write_to_client in
  (try loop session with Wire.Bad_header h -> prerr_endline ("elpi-dap: bad DAP header: " ^ h));
  Option.iter Debuggee.kill session.Session.debuggee
