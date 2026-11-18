(* The debuggee: elpi-debug -machine, run as a child process, and the
   messages it prints (../../debug/lib/machine.elpi):
   - lines "@@elpi-debug {JSON}": the listing of the program, then one
     description per stop (in place of the prompt);
   - any other line: text for a person (the events shown, the output of a
     command, the prints of the program, the solutions). *)

(* ---- The messages --------------------------------------------------------- *)

type location = { file : string; line : int }

(* A rule of the program, with its number in the listing (the N of the
   commands + clause N, - clause N). *)
type rule = { number : int; predicate : string; at : location }

type program = { rules : rule list; declarations : location list }

(* The clause a call runs: a rule, a hypothetical clause (added by =>), or
   none (at the ports of the call itself, before or after its clauses). *)
type running = Rule_at of location | Hypothesis of string | No_clause

type argument = { mode : string; value : string }

(* A logic variable of a goal and the eigenvariables it may depend on. *)
type var_scope = { var : string; depends : string list }

(* A call of the stack; the call 0 is the query. *)
type frame = { id : int; goal : string; running : running; args : argument list; scope : var_scope list }

(* A binding made by the head unification of a unify step. *)
type binding = { bound : string; bound_to : string; pruning : string }

(* A clause of the local program and the call that added it. *)
type hypothesis = { clause : string; origin : string }

(* A stop: its number (a command that only shows something prompts again
   with the same number), why it stops (start, step, breakpoint, pause),
   the event (its port and its text) and the state of the run there. *)
type stop = {
  stop_number : int;
  reason : string;
  port : string;
  text : string;
  frames : frame list;  (* the call in focus first *)
  bindings : binding list;
  hypotheses : hypothesis list;
  eigenvariables : string list;
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

let argument_of json = { mode = string_field "mode" json; value = string_field "value" json }

let var_scope_of json = { var = string_field "var" json; depends = list_field "depends" J.to_string json }

let frame_of json =
  {
    id = int_field "id" json;
    goal = string_field "goal" json;
    running = running_of (J.member "clause" json);
    args = list_field "args" argument_of json;
    scope = list_field "scope" var_scope_of json;
  }

let binding_of json = { bound = string_field "var" json; bound_to = string_field "value" json; pruning = string_field "pruning" json }

let hypothesis_of json = { clause = string_field "clause" json; origin = string_field "origin" json }

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
