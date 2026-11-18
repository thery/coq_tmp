(* A debugging session: the DAP requests of the client (VS Code) turned
   into commands of elpi-debug -machine, and the messages of elpi-debug
   turned into responses and events.

   The mapping (README.md):
   - setBreakpoints (file:line): + clause N, N the rule that holds the line;
     setFunctionBreakpoints: + P, a breakpoint on the predicate P;
   - stepIn: c (creep); next: s (skip) at the ports of a call, c at a step
     inside a call (unify, pi, =>, cut, delay); stepOut: o; continue: l
     (leap); restartFrame: r N (retry the call N); pause: SIGUSR1;
   - stackTrace: the calls of the stop, each at the clause it runs (the
     call in focus, at its own ports, at the clause of its caller: where
     the goal is written);
   - scopes: the goal (its arguments; the bindings of a unify step), the
     local program (the clauses added by =>), the eigenvariables (and what
     each logic variable of the goal may depend on);
   - evaluate (debug console): any command of elpi-debug.

   elpi-debug reads a command at each stop and answers each one by a new
   description of the stop: with the same number if the command only
   showed something or changed a breakpoint, with a new one when the run
   went on to a new stop.  The adapter keeps, in order, what it expects
   from each command sent (an [expectation]); the description that answers
   a command pops its expectation, and the text printed in between belongs
   to it. *)

open Debuggee
module P = Protocol

(* What the adapter expects from the next description of a stop. *)
type expectation =
  | Initial_stop  (* the stop Start: elpi-debug is ready (answers launch) *)
  | Quiet  (* a breakpoint changed: its text is not shown *)
  | Answer of P.request * Buffer.t  (* an evaluate: its text is the answer *)
  | Next_stop  (* the run goes on: the next stop is reported *)

type t = {
  write : P.json -> unit;  (* sends a message to the client *)
  mutable next_seq : int;
  mutable debuggee : Debuggee.t option;
  mutable program : program option;
  mutable stop : stop option;  (* the stop in progress, when the run is stopped *)
  expectations : expectation Queue.t;
  mutable launch : P.request option;  (* answered at the stop Start *)
  mutable stop_on_entry : bool;
  mutable lines_start_at_1 : bool;
  mutable errors_text : Buffer.t;  (* what elpi-debug wrote on stderr *)
  clause_breakpoints : (string, int list) Hashtbl.t;  (* file -> the rules with a breakpoint *)
  mutable function_breakpoints : string list;
  mutable terminated : bool;  (* the event terminated was sent *)
  mutable finished : bool;  (* disconnect answered: the adapter may exit *)
}

let create ~write =
  {
    write;
    next_seq = 1;
    debuggee = None;
    program = None;
    stop = None;
    expectations = Queue.create ();
    launch = None;
    stop_on_entry = false;
    lines_start_at_1 = true;
    errors_text = Buffer.create 256;
    clause_breakpoints = Hashtbl.create 7;
    function_breakpoints = [];
    terminated = false;
    finished = false;
  }

(* ---- Sending ------------------------------------------------------------- *)

let seq s =
  let n = s.next_seq in
  s.next_seq <- n + 1;
  n

let respond s r body = s.write (P.response ~seq:(seq s) r ~body)
let fail s r message = s.write (P.error_response ~seq:(seq s) r message)
let emit s name body = s.write (P.event ~seq:(seq s) name body)

(* [output s category text]: an output event (category stdout, stderr or
   console). *)
let output s category text = emit s "output" (`Assoc [ ("category", `String category); ("output", `String text) ])

let thread_id = 1

(* [send_command s command expectation]: a command to elpi-debug, and what
   to expect from it. *)
let send_command s command expectation =
  match s.debuggee with
  | None -> ()
  | Some d ->
      Queue.add expectation s.expectations;
      Debuggee.send d command

(* [resume s command]: a command that lets the run go on; the next stop is
   reported to the client. *)
let resume s command =
  s.stop <- None;
  send_command s command Next_stop

(* [running s]: a command let the run go on, and no stop came yet. *)
let running s = s.debuggee <> None && s.stop = None

(* ---- Stops ---------------------------------------------------------------- *)

(* [dap_reason stop]: the reason of a stopped event. *)
let dap_reason stop =
  match stop.reason with "start" -> "entry" | "breakpoint" -> "breakpoint" | "pause" -> "pause" | _ -> "step"

(* [ports_of_calls]: the ports of a call (the others are steps inside one). *)
let ports_of_calls = [ "Call"; "Exit"; "Redo"; "Fail"; "Resume" ]

let description stop = if List.mem stop.port ports_of_calls then stop.port ^ " port" else stop.port ^ " step"

(* [report_stop s stop]: the stopped event of a new stop. *)
let report_stop s stop =
  emit s "stopped"
    (`Assoc
      [ ("reason", `String (dap_reason stop)); ("description", `String (description stop));
        ("text", `String stop.text); ("threadId", `Int thread_id); ("allThreadsStopped", `Bool true) ])

(* [on_stop s stop]: elpi-debug describes a stop, answering the oldest
   command sent. *)
let on_stop s stop =
  s.stop <- Some stop;
  match Queue.take_opt s.expectations with
  | Some Initial_stop -> (
      match s.launch with
      | Some r ->
          s.launch <- None;
          respond s r `Null;
          emit s "initialized" `Null
      | None -> ())
  | Some Quiet -> ()
  | Some (Answer (r, text)) -> respond s r (`Assoc [ ("result", `String (Buffer.contents text)); ("variablesReference", `Int 0) ])
  | Some Next_stop | None -> report_stop s stop

(* [on_text s line]: a line of text of elpi-debug, which belongs to the
   oldest command sent. *)
let on_text s line =
  match Queue.peek_opt s.expectations with
  | Some Quiet -> ()
  | Some (Answer (_, text)) -> Buffer.add_string text (line ^ "\n")
  | Some (Initial_stop | Next_stop) | None -> output s "stdout" (line ^ "\n")

(* [on_debuggee_line s line]: a line of elpi-debug's stdout. *)
let on_debuggee_line s line =
  match Debuggee.message_of_line line with
  | Program p -> s.program <- Some (Breakpoints.with_canonical_files p)
  | Stop stop -> on_stop s stop
  | Text text -> on_text s text
  | exception Debuggee.Bad_message msg -> output s "console" ("elpi-dap: unreadable message of elpi-debug: " ^ msg ^ "\n")

(* [on_debuggee_error_line s line]: a line of elpi-debug's stderr. *)
let on_debuggee_error_line s line =
  Buffer.add_string s.errors_text (line ^ "\n");
  output s "stderr" (line ^ "\n")

(* [terminate s]: the events of the end of the session, once. *)
let terminate s =
  if not s.terminated then begin
    s.terminated <- true;
    emit s "terminated" `Null
  end

(* [on_debuggee_end s]: elpi-debug exited; the commands still expected get
   no answer. *)
let on_debuggee_end s =
  match s.debuggee with
  | None -> ()
  | Some d ->
      let code = Debuggee.exit_code d in
      s.debuggee <- None;
      s.stop <- None;
      (match s.launch with
       | Some r ->
           s.launch <- None;
           fail s r ("elpi-debug stopped before the start of the run:\n" ^ Buffer.contents s.errors_text)
       | None -> ());
      Queue.iter
        (function Answer (r, _) -> fail s r "elpi-debug exited" | Initial_stop | Quiet | Next_stop -> ())
        s.expectations;
      Queue.clear s.expectations;
      emit s "exited" (`Assoc [ ("exitCode", `Int code) ]);
      terminate s

(* ---- Frames and variables ----------------------------------------------------------- *)

(* [client_line s line]: a line number as the client counts them. *)
let client_line s line = if s.lines_start_at_1 then line else line - 1

(* [current_frames s]: the calls of the stop in progress. *)
let current_frames s = match s.stop with Some stop -> stop.frames | None -> []

(* [frame_location frames index]: where the call [index] of the stack is:
   at the clause it runs; at its own ports, where it runs no clause, at the
   clause of its caller. *)
let rec frame_location frames index =
  match List.nth_opt frames index with
  | None -> No_clause
  | Some f -> ( match f.running with No_clause -> frame_location frames (index + 1) | place -> place)

let source_of file = `Assoc [ ("name", `String (Filename.basename file)); ("path", `String file) ]

(* [stack_frame s stop index f]: the DAP stack frame of the call f; the
   name of the call in focus starts with the port of the stop. *)
let stack_frame s stop index f =
  let name = if f.id = 0 then f.goal else Printf.sprintf "#%d %s" f.id f.goal in
  let name = if index = 0 then stop.port ^ ": " ^ name else name in
  let common = [ ("id", `Int f.id); ("column", `Int (if s.lines_start_at_1 then 1 else 0)) ] in
  match frame_location stop.frames index with
  | Rule_at at -> `Assoc ((("name", `String name) :: common) @ [ ("source", source_of at.file); ("line", `Int (client_line s at.line)) ])
  | Hypothesis origin -> `Assoc ((("name", `String (name ^ "   (" ^ origin ^ ")")) :: common) @ [ ("line", `Int 0) ])
  | No_clause -> `Assoc ((("name", `String name) :: common) @ [ ("line", `Int 0) ])

(* The scopes of a frame: references index * 3 + 1, + 2, + 3 (index: its
   place in the stack, from 0); valid while the stop lasts. *)
type scope = Goal | Local_program | Eigenvariables

let scope_reference index scope = (index * 3) + match scope with Goal -> 1 | Local_program -> 2 | Eigenvariables -> 3

let scope_of_reference reference =
  let index = (reference - 1) / 3 in
  match (reference - 1) mod 3 with 0 -> (index, Goal) | 1 -> (index, Local_program) | _ -> (index, Eigenvariables)

let variable name value = `Assoc [ ("name", `String name); ("value", `String value); ("variablesReference", `Int 0) ]

(* [goal_variables stop index f]: the goal, its arguments, and for the call
   in focus at a unify step, the bindings it made. *)
let goal_variables stop index f =
  let argument k (a : argument) = variable (Printf.sprintf "arg %d (%s)" (k + 1) a.mode) a.value in
  let binding (b : binding) = variable (b.bound ^ " :=") (b.bound_to ^ b.pruning) in
  let bindings = if index = 0 then List.map binding stop.bindings else [] in
  (variable "goal" f.goal :: List.mapi argument f.args) @ bindings

let local_program_variables stop = List.map (fun h -> variable h.clause h.origin) stop.hypotheses

(* [eigenvariable_variables stop f]: the eigenvariables in force, then
   what each logic variable of the goal may depend on. *)
let eigenvariable_variables stop f =
  let in_force e = variable e "eigenvariable in force" in
  let depends (v : var_scope) =
    variable v.var (match v.depends with [] -> "may depend on no eigenvariable" | es -> "may depend on " ^ String.concat ", " es)
  in
  List.map in_force stop.eigenvariables @ List.map depends f.scope

(* ---- Breakpoints ----------------------------------------------------------------------- *)

(* [set_clause_breakpoints s r]: the breakpoints of a file, as breakpoints
   on the rules that hold their lines. *)
let set_clause_breakpoints s (r : P.request) program =
  let path = Option.value ~default:"" (Yojson.Safe.Util.to_string_option (P.field "path" (P.argument "source" r))) in
  let file = Breakpoints.canonical path in
  let lines = List.filter_map (fun b -> Yojson.Safe.Util.to_int_option (P.field "line" b)) (P.list_argument "breakpoints" r) in
  let line_of_client line = if s.lines_start_at_1 then line else line + 1 in
  let found = List.map (fun line -> Breakpoints.rule_at program ~file ~line:(line_of_client line)) lines in
  let answer = function
    | Some (rule : rule) -> `Assoc [ ("verified", `Bool true); ("line", `Int (client_line s rule.at.line)) ]
    | None -> `Assoc [ ("verified", `Bool false); ("message", `String "no clause at this line") ]
  in
  let numbers = List.sort_uniq compare (List.filter_map (Option.map (fun (rule : rule) -> rule.number)) found) in
  let before = Option.value ~default:[] (Hashtbl.find_opt s.clause_breakpoints file) in
  Hashtbl.replace s.clause_breakpoints file numbers;
  List.iter
    (fun (sign, n) -> send_command s (Printf.sprintf "%s clause %d" sign n) Quiet)
    (Breakpoints.changes ~before ~after:numbers);
  respond s r (`Assoc [ ("breakpoints", `List (List.map answer found)) ])

(* [set_function_breakpoints s r]: breakpoints on predicates (the call
   port of each of their calls). *)
let set_function_breakpoints s (r : P.request) program =
  let names = List.filter_map (fun b -> Yojson.Safe.Util.to_string_option (P.field "name" b)) (P.list_argument "breakpoints" r) in
  let names = List.map String.trim names in
  let unique = List.sort_uniq compare names in
  List.iter
    (fun (sign, name) -> send_command s (Printf.sprintf "%s %s" sign name) Quiet)
    (Breakpoints.changes ~before:s.function_breakpoints ~after:unique);
  s.function_breakpoints <- unique;
  let answer name =
    if Breakpoints.has_rules program name then `Assoc [ ("verified", `Bool true) ]
    else `Assoc [ ("verified", `Bool true); ("message", `String ("the program has no rule for " ^ name)) ]
  in
  respond s r (`Assoc [ ("breakpoints", `List (List.map answer names)) ])

(* ---- Requests ------------------------------------------------------------------------ *)

let capabilities =
  `Assoc
    [ ("supportsConfigurationDoneRequest", `Bool true); ("supportsFunctionBreakpoints", `Bool true);
      ("supportsRestartFrame", `Bool true); ("supportsTerminateRequest", `Bool true);
      ("supportsEvaluateForHovers", `Bool false); ("supportsStepBack", `Bool false) ]

(* [default_elpi_debug ()]: elpi-debug next to this executable (both are
   installed in the same bin directory: the directory of the command as it
   was called, which may be a symbolic link, or of the executable file),
   else elpi-debug from the PATH. *)
let default_elpi_debug () =
  let next_to path = Filename.concat (Filename.dirname path) "elpi-debug" in
  let called_as = Sys.argv.(0) in
  let candidates = (if String.contains called_as '/' then [ next_to called_as ] else []) @ [ next_to Sys.executable_name ] in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> "elpi-debug"

let launch s (r : P.request) =
  match P.string_argument "program" r, P.string_argument "goal" r with
  | None, _ | _, None -> fail s r "launch needs a program (an .elpi file) and a goal"
  | Some program, Some goal ->
      let exe = Option.value ~default:(default_elpi_debug ()) (P.string_argument "elpiDebug" r) in
      let options = List.filter_map Yojson.Safe.Util.to_string_option (P.list_argument "args" r) in
      let cwd = P.string_argument "cwd" r in
      s.stop_on_entry <- P.bool_argument "stopOnEntry" ~default:false r;
      s.launch <- Some r;
      s.debuggee <- Some (Debuggee.start ~exe ~cwd ~options ~program ~goal);
      Queue.add Initial_stop s.expectations

(* [with_stop s r k]: k on the stop in progress, or a failure if the run is
   not stopped. *)
let with_stop s r k = match s.stop with Some stop -> k stop | None -> fail s r "the program is not stopped"

let with_program s r k = match s.program with Some p -> k p | None -> fail s r "the program is not launched yet"

(* [next_command stop]: step over: skip the call at its ports, creep at a
   step inside it (skip would leave the call). *)
let next_command stop = if List.mem stop.port ports_of_calls then "s" else "c"

(* The commands of elpi-debug that let the run go on (the others only show
   something or change a breakpoint). *)
let resuming_commands = [ ""; "c"; "s"; "o"; "l"; "t"; "n"; "r"; "f"; "a" ]

let first_word text = match String.split_on_char ' ' (String.trim text) with w :: _ -> w | [] -> ""

let evaluate s (r : P.request) =
  let expression = Option.value ~default:"" (P.string_argument "expression" r) in
  if P.string_argument "context" r <> Some "repl" then fail s r "only commands of elpi-debug in the debug console"
  else
    with_stop s r (fun _ ->
        if List.mem (first_word expression) resuming_commands then begin
          respond s r (`Assoc [ ("result", `String ""); ("variablesReference", `Int 0) ]);
          emit s "continued" (`Assoc [ ("threadId", `Int thread_id) ]);
          resume s expression
        end
        else send_command s expression (Answer (r, Buffer.create 256)))

let stack_trace s (r : P.request) =
  with_stop s r (fun stop ->
      let frames = List.mapi (stack_frame s stop) stop.frames in
      respond s r (`Assoc [ ("stackFrames", `List frames); ("totalFrames", `Int (List.length frames)) ]))

(* [frame_index stop id]: the place in the stack of the call id. *)
let frame_index stop id =
  let rec find k = function [] -> None | f :: fs -> if f.id = id then Some k else find (k + 1) fs in
  find 0 stop.frames

let scopes s (r : P.request) =
  with_stop s r (fun stop ->
      match Option.bind (P.int_argument "frameId" r) (frame_index stop) with
      | None -> fail s r "no such frame"
      | Some index ->
          let scope name hint kind =
            `Assoc
              [ ("name", `String name); ("presentationHint", `String hint);
                ("variablesReference", `Int (scope_reference index kind)); ("expensive", `Bool false) ]
          in
          respond s r
            (`Assoc
              [ ("scopes",
                 `List [ scope "Goal" "arguments" Goal; scope "Local program (=>)" "locals" Local_program;
                         scope "Eigenvariables" "locals" Eigenvariables ]) ]))

let variables s (r : P.request) =
  let empty () = respond s r (`Assoc [ ("variables", `List []) ]) in
  match s.stop, P.int_argument "variablesReference" r with
  | Some stop, Some reference when reference > 0 -> (
      let index, kind = scope_of_reference reference in
      match List.nth_opt stop.frames index with
      | None -> empty ()
      | Some f ->
          let vars =
            match kind with
            | Goal -> goal_variables stop index f
            | Local_program -> local_program_variables stop
            | Eigenvariables -> eigenvariable_variables stop f
          in
          respond s r (`Assoc [ ("variables", `List vars) ]))
  | _ -> empty ()

(* [step s r command]: a stepping request, answered at once; the stop it
   leads to is reported by a stopped event. *)
let step s r command =
  with_stop s r (fun stop ->
      respond s r (if r.P.command = "continue" then `Assoc [ ("allThreadsContinued", `Bool true) ] else `Null);
      resume s (command stop))

let restart_frame s (r : P.request) =
  with_stop s r (fun _ ->
      match P.int_argument "frameId" r with
      | Some id when id > 0 ->
          respond s r `Null;
          resume s (Printf.sprintf "r %d" id)
      | _ -> fail s r "the query itself cannot be restarted")

let configuration_done s r =
  respond s r `Null;
  match s.stop with
  | Some stop when s.stop_on_entry -> report_stop s stop
  | Some _ -> resume s "l"
  | None -> ()

(* [end_session s r ~exit]: terminate or disconnect: elpi-debug is ended;
   after disconnect the adapter exits. *)
let end_session s r ~exit =
  Option.iter Debuggee.kill s.debuggee;
  respond s r `Null;
  if exit then s.finished <- true

let on_request s (r : P.request) =
  match r.command with
  | "initialize" ->
      s.lines_start_at_1 <- P.bool_argument "linesStartAt1" ~default:true r;
      respond s r capabilities
  | "launch" -> launch s r
  | "setBreakpoints" -> with_program s r (set_clause_breakpoints s r)
  | "setFunctionBreakpoints" -> with_program s r (set_function_breakpoints s r)
  | "setExceptionBreakpoints" -> respond s r (`Assoc [ ("breakpoints", `List []) ])
  | "configurationDone" -> configuration_done s r
  | "threads" -> respond s r (`Assoc [ ("threads", `List [ `Assoc [ ("id", `Int thread_id); ("name", `String "elpi") ] ]) ])
  | "stackTrace" -> stack_trace s r
  | "scopes" -> scopes s r
  | "variables" -> variables s r
  | "continue" -> step s r (fun _ -> "l")
  | "next" -> step s r next_command
  | "stepIn" -> step s r (fun _ -> "c")
  | "stepOut" -> step s r (fun _ -> "o")
  | "restartFrame" -> restart_frame s r
  | "pause" ->
      if running s then Option.iter Debuggee.ask_pause s.debuggee;
      respond s r `Null
  | "evaluate" -> evaluate s r
  | "terminate" -> end_session s r ~exit:false
  | "disconnect" -> end_session s r ~exit:true
  | other -> fail s r ("elpi-dap does not support " ^ other)

(* [debuggee_inputs s]: what the main loop reads from elpi-debug. *)
let debuggee_inputs s = match s.debuggee with Some d -> [ (d.output, `Output); (d.errors, `Errors) ] | None -> []
