(* dap_replay ADAPTER SCRIPT: play a scripted DAP session with the debug
   adapter ADAPTER (a client in place of VS Code), and print it.

   The script has one JSON object per line (empty lines and lines starting
   with # are printed as they are, for the reader):
   - a request, {"command": C, "arguments": A}: sent with the next sequence
     number; then the replay waits for its response;
   - {"await": E}: wait for the event E (stopped, terminated...).
   The transcript shows each message sent ("->") and received ("<-"), one
   JSON object per line, in order.  A message is printed when the script
   waits for it or for a later one; so the transcript does not depend on
   timing, provided the script waits for the last message of each step.
   At the end of the script the replay closes the adapter's stdin and
   prints what is left. *)

let timeout = 30.0

let fail fmt = Printf.ksprintf (fun s -> print_endline ("dap_replay: " ^ s); exit 1) fmt

(* ---- The adapter, as a child process ------------------------------------ *)

type adapter = { pid : int; to_adapter : Unix.file_descr; from_adapter : Unix.file_descr; pending : Buffer.t }

let start_adapter exe =
  let in_r, in_w = Unix.pipe ~cloexec:true () in
  let out_r, out_w = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process exe [| exe |] in_r out_w Unix.stderr in
  Unix.close in_r;
  Unix.close out_w;
  { pid; to_adapter = in_w; from_adapter = out_r; pending = Buffer.create 4096 }

let send a json =
  let body = Yojson.Safe.to_string json in
  print_endline ("-> " ^ body);
  let framed = Printf.sprintf "Content-Length: %d\r\n\r\n%s" (String.length body) body in
  ignore (Unix.write_substring a.to_adapter framed 0 (String.length framed))

(* [read_more a]: wait for bytes from the adapter; false at its end. *)
let read_more a =
  match Unix.select [ a.from_adapter ] [] [] timeout with
  | [], _, _ -> fail "no message from the adapter for %.0f s" timeout
  | _ ->
      let chunk = Bytes.create 65536 in
      let n = Unix.read a.from_adapter chunk 0 (Bytes.length chunk) in
      Buffer.add_subbytes a.pending chunk 0 n;
      n > 0

(* [split_message s]: the body of the first complete message of s and
   the rest. *)
let split_message s =
  let header_end = "\r\n\r\n" in
  let rec find k = if k + 4 > String.length s then None else if String.sub s k 4 = header_end then Some k else find (k + 1) in
  match find 0 with
  | None -> None
  | Some k ->
      let header = String.sub s 0 k in
      let length = Scanf.sscanf header "Content-Length: %d" (fun n -> n) in
      let start = k + 4 in
      if String.length s < start + length then None
      else Some (String.sub s start length, String.sub s (start + length) (String.length s - start - length))

(* [next_message a]: the next message of the adapter, None at its end. *)
let rec next_message a =
  match split_message (Buffer.contents a.pending) with
  | Some (body, rest) ->
      Buffer.clear a.pending;
      Buffer.add_string a.pending rest;
      Some (Yojson.Safe.from_string body)
  | None -> if read_more a then next_message a else None

(* [receive_until a wanted]: print the messages of the adapter up to the
   first one that satisfies wanted. *)
let rec receive_until a wanted what =
  match next_message a with
  | None -> fail "the adapter ended while waiting for %s" what
  | Some json ->
      print_endline ("<- " ^ Yojson.Safe.to_string json);
      if not (wanted json) then receive_until a wanted what

(* ---- The script ---------------------------------------------------------- *)

let field name json = Yojson.Safe.Util.member name json

let is_response_to seq json = field "type" json = `String "response" && field "request_seq" json = `Int seq
let is_event name json = field "type" json = `String "event" && field "event" json = `String name

let play a lines =
  let seq = ref 0 in
  let step line =
    if String.trim line = "" || line.[0] = '#' then print_endline line
    else
      let json = Yojson.Safe.from_string line in
      match field "await" json, field "command" json with
      | `String event, _ -> receive_until a (is_event event) ("the event " ^ event)
      | _, `String command ->
          incr seq;
          let arguments = match field "arguments" json with `Null -> `Assoc [] | args -> args in
          send a (`Assoc [ ("seq", `Int !seq); ("type", `String "request"); ("command", `String command); ("arguments", arguments) ]);
          receive_until a (is_response_to !seq) ("the response to " ^ command)
      | _ -> fail "not a request nor an await: %s" line
  in
  List.iter step lines

let rec print_rest a =
  match next_message a with
  | Some json ->
      print_endline ("<- " ^ Yojson.Safe.to_string json);
      print_rest a
  | None -> ()

let () =
  match Sys.argv with
  | [| _; exe; script |] ->
      Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
      let lines = In_channel.with_open_text script In_channel.input_all |> String.split_on_char '\n' in
      let lines = match List.rev lines with "" :: rest -> List.rev rest | _ -> lines in
      let a = start_adapter exe in
      play a lines;
      Unix.close a.to_adapter;
      print_rest a;
      (match Unix.waitpid [] a.pid with
       | _, Unix.WEXITED 0 -> ()
       | _, Unix.WEXITED n -> print_endline (Printf.sprintf "dap_replay: the adapter exited with code %d" n)
       | _ -> print_endline "dap_replay: the adapter was killed")
  | _ -> fail "usage: dap_replay ADAPTER SCRIPT"
