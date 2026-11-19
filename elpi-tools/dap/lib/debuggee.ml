(* The debuggee: elpi-debug -machine, run as a child process, and the
   messages it prints (../../debug/lib/machine.elpi):
   - lines "@@elpi-debug {JSON}": the listing of the program, then one
     description per stop (in place of the prompt);
   - any other line: text for a person (the events shown, the output of a
     command, the prints of the program, the solutions). *)

(* ---- The messages --------------------------------------------------------- *)

type location = { file : string; line : int }

(* A rule of the program, or a CHR rule (numbered after the rules), with
   its number in the listing (the N of the commands + clause N,
   - clause N). *)
type rule = { number : int; predicate : string; at : location }

type program = { rules : rule list; declarations : location list }

(* The clause a call runs: a rule, a hypothetical clause (added by =>), or
   none (at the ports of the call itself, before or after its clauses). *)
type running = Rule_at of location | Hypothesis of string | No_clause

(* A range of a file: from line, column to end_line, end_column, the
   position just after its last character (lines from 1, columns from 0). *)
type span = { span_file : string; start_line : int; start_column : int; end_line : int; end_column : int }

(* Where a call is written: the goal [index] (from 1) of the body of the
   clause [written_in], and the place of that goal in the source (none for
   a hypothetical clause). *)
type premise = { index : int; written_in : running; place : span option }

type argument = { mode : string; value : string }

(* A logic variable of a goal and the eigenvariables it may depend on. *)
type var_scope = { var : string; depends : string list }

(* A call of the stack; the call 0 is the query. *)
type frame = {
  id : int;
  goal : string;
  running : running;
  premise : premise option;  (* none for a call of the query or a woken goal *)
  args : argument list;
  scope : var_scope list;
}

(* A binding made by the step of the stop: the head unification of a unify
   step, or the whole call at an exit port (the variable named X<n>). *)
type binding = { bound : string; bound_to : string; pruning : string }

(* A clause of the local program and the call that added it. *)
type hypothesis = { clause : string; origin : string }

(* A variable of the query, by its source name, and its value at the stop. *)
type query_var = { name : string; value : string }

(* A goal of the constraint store and the number of its suspension (0 when
   not numbered). *)
type stored = { suspension : int; stored_goal : string }

(* A stop: its number (a command that only shows something prompts again
   with the same number), why it stops (start, step, breakpoint, pause),
   the event (its port and its text) and the state of the run there, the
   constraint store included. *)
type stop = {
  stop_number : int;
  reason : string;
  port : string;
  text : string;
  frames : frame list;  (* the call in focus first *)
  bindings : binding list;
  hypotheses : hypothesis list;
  eigenvariables : string list;
  query_vars : query_var list;  (* the variables of the query, by their source names *)
  store : stored list;  (* the constraint store, most recent first *)
  rule : location option;  (* at a stop at a CHR rule (its attempt, its outcome): the rule *)
}

type message = Program of program | Stop of stop | Text of string

(* ---- Reading the messages ---------------------------------------------------- *)

let machine_prefix = "@@elpi-debug "

module J = Yojson.Safe.Util

let string_field name json = J.to_string (J.member name json)
let int_field name json = J.to_int (J.member name json)
let list_field name read json = List.map read (J.to_list (J.member name json))

let location_of json = { file = string_field "file" json; line = int_field "line" json }

let rule_of json = { number = int_field "clause" json; predicate = string_field "predicate" json; at = location_of json }

let running_of json =
  match json with
  | `Null -> No_clause
  | `Assoc fields when List.mem_assoc "hypothesis" fields -> Hypothesis (string_field "hypothesis" json)
  | _ -> Rule_at (location_of json)

let span_of json =
  {
    span_file = string_field "file" json;
    start_line = int_field "line" json;
    start_column = int_field "column" json;
    end_line = int_field "endLine" json;
    end_column = int_field "endColumn" json;
  }

(* [premise_of json]: the field "premise" of a frame (null, or absent from
   an older elpi-debug, when the premise is not known). *)
let premise_of = function
  | `Null -> None
  | json ->
      let place = match J.member "place" json with `Null -> None | p -> Some (span_of p) in
      Some { index = int_field "index" json; written_in = running_of (J.member "clause" json); place }

let argument_of json = { mode = string_field "mode" json; value = string_field "value" json }

let var_scope_of json = { var = string_field "var" json; depends = list_field "depends" J.to_string json }

let frame_of json =
  {
    id = int_field "id" json;
    goal = string_field "goal" json;
    running = running_of (J.member "clause" json);
    premise = premise_of (J.member "premise" json);
    args = list_field "args" argument_of json;
    scope = list_field "scope" var_scope_of json;
  }

let binding_of json = { bound = string_field "var" json; bound_to = string_field "value" json; pruning = string_field "pruning" json }

let hypothesis_of json = { clause = string_field "clause" json; origin = string_field "origin" json }

let query_var_of json = { name = string_field "name" json; value = string_field "value" json }

let stored_of json = { suspension = int_field "suspension" json; stored_goal = string_field "goal" json }

(* [optional_list name read json]: the list field [name], empty when absent
   (from an older elpi-debug) *)
let optional_list name read json = match J.member name json with `Null -> [] | l -> List.map read (J.to_list l)

let stop_of json =
  {
    stop_number = int_field "stop" json;
    reason = string_field "reason" json;
    port = string_field "port" json;
    text = string_field "text" json;
    frames = list_field "frames" frame_of json;
    bindings = list_field "bindings" binding_of json;
    hypotheses = list_field "hyps" hypothesis_of json;
    eigenvariables = list_field "eigenvariables" J.to_string json;
    query_vars = list_field "query" query_var_of json;
    store = optional_list "store" stored_of json;
    rule = (match J.member "rule" json with `Null -> None | l -> Some (location_of l));
  }

let program_of json = { rules = list_field "clauses" rule_of json; declarations = list_field "declarations" location_of json }

exception Bad_message of string

(* [message_of_json json]: the message of a machine line. *)
let message_of_json json =
  match string_field "event" json with
  | "program" -> Program (program_of json)
  | "stop" -> Stop (stop_of json)
  | other -> raise (Bad_message ("unknown message " ^ other))

(* [message_of_line line]: the message of a line of elpi-debug. *)
let message_of_line line =
  let n = String.length machine_prefix in
  if String.length line < n || String.sub line 0 n <> machine_prefix then Text line
  else
    try message_of_json (Yojson.Safe.from_string (String.sub line n (String.length line - n)))
    with J.Type_error (msg, _) | Yojson.Json_error msg -> raise (Bad_message msg)

(* ---- The process ------------------------------------------------------------------ *)

type t = {
  pid : int;
  commands : Unix.file_descr;  (* its stdin *)
  output : Wire.input;  (* its stdout *)
  errors : Wire.input;  (* its stderr *)
}

(* [start ~exe ~cwd ~options ~program ~goal]: run [exe -machine options
   program goal] in the directory cwd (if given). *)
let start ~exe ~cwd ~options ~program ~goal =
  let argv = Array.of_list ((exe :: "-machine" :: options) @ [ program; goal ]) in
  let stdin_r, stdin_w = Unix.pipe ~cloexec:true () in
  let stdout_r, stdout_w = Unix.pipe ~cloexec:true () in
  let stderr_r, stderr_w = Unix.pipe ~cloexec:true () in
  match Unix.fork () with
  | 0 -> (
      try
        Unix.dup2 stdin_r Unix.stdin;
        Unix.dup2 stdout_w Unix.stdout;
        Unix.dup2 stderr_w Unix.stderr;
        Option.iter Unix.chdir cwd;
        Unix.execvp exe argv
      with e ->
        prerr_endline ("elpi-dap: cannot run " ^ exe ^ ": " ^ Printexc.to_string e);
        Unix._exit 127)
  | pid ->
      List.iter Unix.close [ stdin_r; stdout_w; stderr_w ];
      { pid; commands = stdin_w; output = Wire.input stdout_r; errors = Wire.input stderr_r }

(* [send t command]: a command line for the prompt of elpi-debug. *)
let send t command = try Wire.write_all t.commands (command ^ "\n") with Unix.Unix_error _ -> ()

(* [ask_pause t]: the run stops at its next event (elpi-debug listens to
   SIGUSR1 with -machine). *)
let ask_pause t = try Unix.kill t.pid Sys.sigusr1 with Unix.Unix_error _ -> ()

(* [kill t]: end the process (when the session ends before the run). *)
let kill t = try Unix.kill t.pid Sys.sigterm with Unix.Unix_error _ -> ()

(* [ended t]: elpi-debug closed its outputs (it exited). *)
let ended t = t.output.closed && t.errors.closed

(* [exit_code t]: the exit code of the process, once it ended. *)
let exit_code t =
  Unix.close t.commands;
  match Unix.waitpid [] t.pid with
  | _, Unix.WEXITED n -> n
  | _, (Unix.WSIGNALED _ | Unix.WSTOPPED _) -> 128
  | exception Unix.Unix_error _ -> 128
