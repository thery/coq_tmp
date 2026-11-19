(* A debugging session: the DAP requests of the client (VS Code) turned
   into commands of elpi-debug -machine, and the messages of elpi-debug
   turned into responses and events.

   The mapping (README.md):
   - setBreakpoints (file:line): + clause N, N the rule (or CHR rule) that
     holds the line;
     setFunctionBreakpoints: + P, a breakpoint on the predicate P;
   - stepIn: c (creep); next: s (skip) at the ports of a call, c at a step
     inside a call (unify, pi, =>, cut, delay); stepOut: o; continue: l
     (leap); restartFrame: r N (retry the call N); pause: SIGUSR1;
   - stackTrace: the calls of the stop; a call at its own ports at the
     goal it comes from (the premise of its caller's clause, a range), a
     caller at the goal of the call it made, the call in focus inside a
     clause at the line of that clause;
   - scopes: the goal (its arguments; the bindings of a unify step or of
     an exit port), the query (its variables by their source names, with
     their values), the local program (the clauses added by =>), the
     eigenvariables (and what each logic variable of the goal may depend
     on), the constraint store;
   - evaluate: in the debug console, any command of elpi-debug; a watch
     expression, a variable of the query by its name, or a variable X3
     (as elpi-debug names it), from the description of the stop.

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
  | Answer of P.request * Buffer.t  (* an evaluate in the debug console: its text is the answer *)
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
  mutable query : string;  (* the goal of the launch *)
  mutable query_place : (string * int) option;
      (* where the query is written (launch's queryPath and queryLine): the
         place of the frames that run no clause yet *)
  mutable lines_start_at_1 : bool;
  mutable columns_start_at_1 : bool;
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
    query = "";
    query_place = None;
    lines_start_at_1 = true;
    columns_start_at_1 = true;
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

(* [client_column s column]: a column (from 0) as the client counts them. *)
let client_column s column = if s.columns_start_at_1 then column + 1 else column

(* [current_frames s]: the calls of the stop in progress. *)
let current_frames s = match s.stop with Some stop -> stop.frames | None -> []

(* Where a call of the stack is shown: a range of a file (the goal of a
   clause being run), the line of a clause, a hypothetical clause, no
   clause, or (the call in focus at a stop at a CHR rule) the line of the
   rule. *)
type shown_at = Range of span | Line of location | In_hypothesis of string | Nowhere | At_rule of location

(* [premise_in at f]: the place of the goal that the call f comes from,
   when that goal is a premise of the rule at [at]. *)
let premise_in (at : location) (f : frame) =
  match f.premise with
  | Some { written_in = Rule_at w; place = Some span; _ } when w = at -> Some span
  | _ -> None

(* [frame_location frames index]: where the call [index] of the stack is.
   In the clause it runs: at the goal of that clause that made the call
   just below it in the stack (index - 1), as debuggers show a caller at
   the call it made; for the call in focus, at the clause.  At its own
   ports, where it runs no clause: at the goal it comes from, where it is
   written (at the line of the CHR rule, for a goal of a rule); for a call
   with no such goal (of the query, or woken), where its caller is. *)
let rec frame_location frames index =
  match List.nth_opt frames index with
  | None -> Nowhere
  | Some f -> (
      match f.running with
      | Rule_at at -> (
          match Option.bind (if index > 0 then List.nth_opt frames (index - 1) else None) (premise_in at) with
          | Some span -> Range span
          | None -> Line at)
      | Hypothesis origin -> In_hypothesis origin
      | No_clause -> (
          match f.premise with
          | Some { place = Some span; _ } -> Range span
          | Some { written_in = Rule_at at; place = None; _ } -> Line at
          | _ -> frame_location frames (index + 1)))

let source_of file = `Assoc [ ("name", `String (Filename.basename file)); ("path", `String file) ]

(* [shown_at stop index]: where the call [index] of the stack of the stop
   is shown: at a stop at a CHR rule (its attempt, its outcome), the call
   in focus (the one whose constraint the rule was tried on, or the query)
   at the rule; otherwise as [frame_location] says. *)
let shown_at stop index =
  match stop.rule with Some at when index = 0 -> At_rule at | _ -> frame_location stop.frames index

(* [stack_frame s stop index f]: the DAP stack frame of the call f; the
   name of the call in focus starts with the port of the stop (at a CHR
   rule, the name is the text of the event: the rule, the constraints it
   is tried on).  A range is given with its end (endLine, endColumn: the
   position just after its last character), so that the editor highlights
   just that goal. *)
let stack_frame s stop index f =
  let name = if f.id = 0 then f.goal else Printf.sprintf "#%d %s" f.id f.goal in
  let name = if index = 0 then stop.port ^ ": " ^ name else name in
  let frame ?(name = name) ?(column = 0) fields =
    `Assoc ((("name", `String name) :: ("id", `Int f.id) :: ("column", `Int (client_column s column)) :: fields)) in
  let whole_line ?name file line = frame ?name [ ("source", source_of file); ("line", `Int (client_line s line)) ] in
  match shown_at stop index with
  | At_rule at -> whole_line ~name:stop.text at.file at.line
  | Range span ->
      frame ~column:span.start_column
        [ ("source", source_of span.span_file); ("line", `Int (client_line s span.start_line));
          ("endLine", `Int (client_line s span.end_line)); ("endColumn", `Int (client_column s span.end_column)) ]
  | Line at -> whole_line at.file at.line
  | In_hypothesis origin -> frame ~name:(name ^ "   (" ^ origin ^ ")") [ ("line", `Int 0) ]
  | Nowhere -> (
      match s.query_place with
      | Some (file, line) -> whole_line file line
      | None -> frame [ ("line", `Int 0) ])

(* The scopes of a frame: references index * 5 + 1 .. + 5 (index: its
   place in the stack, from 0); valid while the stop lasts. *)
type scope = Goal | Query | Local_program | Eigenvariables | Constraints

let scope_reference index scope =
  (index * 5) + match scope with Goal -> 1 | Query -> 2 | Local_program -> 3 | Eigenvariables -> 4 | Constraints -> 5

let scope_of_reference reference =
  let index = (reference - 1) / 5 in
  match (reference - 1) mod 5 with
  | 0 -> (index, Goal)
  | 1 -> (index, Query)
  | 2 -> (index, Local_program)
  | 3 -> (index, Eigenvariables)
  | _ -> (index, Constraints)

let variable name value = `Assoc [ ("name", `String name); ("value", `String value); ("variablesReference", `Int 0) ]

(* [goal_variables stop index f]: the goal, its arguments, and for the call
   in focus at a unify step, the bindings it made. *)
let goal_variables stop index f =
  let argument k (a : argument) = variable (Printf.sprintf "arg %d (%s)" (k + 1) a.mode) a.value in
  let binding (b : binding) = variable (b.bound ^ " :=") (b.bound_to ^ b.pruning) in
  let bindings = if index = 0 then List.map binding stop.bindings else [] in
  (variable "goal" f.goal :: List.mapi argument f.args) @ bindings

(* [query_variables stop]: the variables of the query, by their source
   names, with their values at the stop (the same for every frame). *)
let query_variables stop = List.map (fun (q : query_var) -> variable q.name q.value) stop.query_vars

let local_program_variables stop = List.map (fun h -> variable h.clause h.origin) stop.hypotheses

(* [constraint_variables stop]: the goals of the constraint store, most
   recent first, each named by its suspension ([S2]; [S?] when not
   numbered), the same for every frame. *)
let constraint_variables stop =
  let name (g : stored) = if g.suspension = 0 then "[S?]" else Printf.sprintf "[S%d]" g.suspension in
  List.map (fun g -> variable (name g) g.stored_goal) stop.store

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
      s.query <- goal;
      s.query_place <-
        (match P.string_argument "queryPath" r, P.int_argument "queryLine" r with
         | Some file, Some line -> Some (file, line)
         | _ -> None);
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

(* [watch_value stop expression]: the value of a watch expression at the
   stop: a variable of the query by its source name (X of the goal [sort
   [2, 1] X]), its value now; a variable as elpi-debug names it (X3): its
   binding by the step of the stop (a unify step, an exit port), else, if
   it is a logic variable of a goal of the stack, that it is unbound; else
   none (it is not in view at this stop). *)
let watch_value stop expression =
  let name = String.trim expression in
  let bound (b : binding) = b.bound = name in
  let in_goal f = List.exists (fun (v : var_scope) -> v.var = name) f.scope in
  match List.find_opt (fun (q : query_var) -> q.name = name) stop.query_vars with
  | Some q -> Some q.value
  | None -> (
      match List.find_opt bound stop.bindings with
      | Some b -> Some (b.bound_to ^ b.pruning)
      | None -> if List.exists in_goal stop.frames then Some (name ^ "   (unbound)") else None)

(* [watch s r expression]: a watch expression, answered from the
   description of the stop in progress. *)
let watch s r expression =
  with_stop s r (fun stop ->
      match watch_value stop expression with
      | Some value -> respond s r (`Assoc [ ("result", `String value); ("variablesReference", `Int 0) ])
      | None -> fail s r (expression ^ ": not in view at this stop (not a variable of the query, nor of a goal of the stack)"))

(* [evaluate_command s r expression]: a command of elpi-debug typed in the
   debug console: one that lets the run go on, or one whose output is the
   answer. *)
let evaluate_command s r expression =
  with_stop s r (fun _ ->
      if List.mem (first_word expression) resuming_commands then begin
        respond s r (`Assoc [ ("result", `String ""); ("variablesReference", `Int 0) ]);
        emit s "continued" (`Assoc [ ("threadId", `Int thread_id) ]);
        resume s expression
      end
      else send_command s expression (Answer (r, Buffer.create 256)))

(* [evaluate s r]: a command in the debug console, or a watch expression. *)
let evaluate s (r : P.request) =
  let expression = Option.value ~default:"" (P.string_argument "expression" r) in
  match P.string_argument "context" r with
  | Some "watch" -> watch s r expression
  | Some "repl" -> evaluate_command s r expression
  | _ -> fail s r "only commands of elpi-debug in the debug console, and watch expressions"

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
                 `List [ scope "Goal" "arguments" Goal; scope "Query" "locals" Query;
                         scope "Local program (=>)" "locals" Local_program;
                         scope "Eigenvariables" "locals" Eigenvariables;
                         scope "Constraints" "locals" Constraints ]) ]))

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
            | Query -> query_variables stop
            | Local_program -> local_program_variables stop
            | Eigenvariables -> eigenvariable_variables stop f
            | Constraints -> constraint_variables stop
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

(* [configuration_done s r]: the run starts: it stops before the first call
   (stopOnEntry), else it runs to the first breakpoint; the Debug Console
   says which, so that the first stop is not mistaken for nothing. *)
let configuration_done s r =
  respond s r `Null;
  match s.stop with
  | Some stop when s.stop_on_entry ->
      output s "console"
        (Printf.sprintf "Start: %s   (stopped before the first call: F11 steps into it, F5 runs to a breakpoint or to the end)\n" s.query);
      report_stop s stop
  | Some _ ->
      output s "console" (Printf.sprintf "Start: %s   (running to the first breakpoint, or to the end)\n" s.query);
      resume s "l"
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
      s.columns_start_at_1 <- P.bool_argument "columnsStartAt1" ~default:true r;
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
