(* elpi-check [OPTION].. FILE: checks the properties of an Elpi program.

   1. the program is reflected as Elpi facts (elpi-reflect, with the
      declarations of Elpi's builtins);
   2. a driver accumulates reflect.elpi, the program, the facts and the
      checker (check.elpi, written in Elpi), all written in a temporary
      directory with the embedded Elpi files;
   3. the query check.main [options] runs the tests and prints the report.
   The exit code is 0 when every property holds, 1 otherwise, 2 for an
   error.  With -json the report is one JSON object per line
   (lib/machine.elpi). *)

open Elpi

let usage =
  "elpi-check [-n TESTS] [-size SIZE] [-seed SEED] [-p PROPERTY] [-json] [-list] [-I DIR].. [-D VAR].. [-v] FILE\n\
   Checks the properties (property \"name\" Formula) of an Elpi program by random testing."

(* -- Options ------------------------------------------------------------ *)

type options = {
  mutable checker_args : string list;  (* passed to check.main *)
  mutable paths : string list;         (* -I *)
  mutable defines : string list;       (* -D *)
  mutable verbose : bool;              (* -v: print the warnings *)
  mutable json : bool;                 (* -json: the report as JSON lines *)
  mutable file : string option;
}

let parse_options () =
  let o = { checker_args = []; paths = []; defines = []; verbose = false; json = false; file = None } in
  let pass name = Arg.String (fun v -> o.checker_args <- o.checker_args @ [ name; v ]) in
  let spec = [
    ("-n", pass "-n", "TESTS  number of tests per property (default 100)");
    ("-size", pass "-size", "SIZE  maximal size of the generated values (default 20)");
    ("-seed", pass "-seed", "SEED  seed of the random generator (default 1)");
    ("-p", pass "-p", "PROPERTY  check only this property");
    ("-json", Arg.Unit (fun () -> o.json <- true; o.checker_args <- o.checker_args @ [ "-json" ]),
     " the report as one JSON object per line (see lib/machine.elpi)");
    ("-list", Arg.Unit (fun () -> o.checker_args <- o.checker_args @ [ "-list" ]),
     " list the properties and their variables, without testing them");
    ("-I", Arg.String (fun d -> o.paths <- o.paths @ [ d ]), "DIR  search accumulated files in DIR");
    ("-D", Arg.String (fun v -> o.defines <- v :: o.defines), "VAR  define VAR (for :if \"VAR\")");
    ("-v", Arg.Unit (fun () -> o.verbose <- true), " print the warnings of the compiler");
  ] in
  Arg.parse spec (fun f -> o.file <- Some f) usage;
  match o.file with
  | None -> prerr_endline usage; exit 2
  | Some file -> (o, file)

(* -- The temporary directory -------------------------------------------- *)

let write file text = Out_channel.with_open_bin file (fun oc -> output_string oc text)

let temporary_directory () =
  let base = Filename.temp_file "elpi-check" "" in
  Sys.remove base;
  Sys.mkdir base 0o700;
  base

let remove_directory dir =
  Array.iter (fun f -> Sys.remove (Filename.concat dir f)) (Sys.readdir dir);
  Sys.rmdir dir

(* The driver: the declarations, the program, its facts, the checker.
   accumulate takes a unit name: the file without its .elpi *)
let driver ~program ~facts =
  let unit f = Printf.sprintf "accumulate %S.\n" (Filename.remove_extension f) in
  String.concat "" [ unit "reflect.elpi"; unit program; unit facts; unit "check.elpi" ]

(* -- Errors -------------------------------------------------------------- *)

(* An error that stops elpi-check (exit code 2): its messages. *)
exception Stop of string list

let error_text (e : API.Error.t) = Format.asprintf "%a" API.Error.pp e

(* An error in the program shows twice: in the program and in its facts,
   which mention the same constants.  The errors located in the generated
   facts are shown only when there is no other error. *)
let fail_with_errors ?(generated = "") errors =
  let in_generated (e : API.Error.t) =
    match e.loc with Some l -> l.API.Ast.Loc.source_name = generated | None -> false
  in
  let others = List.filter (fun e -> not (in_generated e)) errors in
  let shown = if others = [] then errors else others in
  raise (Stop (List.map error_text shown))

(* [report_stop ~json messages]: the messages on stderr; with -json, also
   one object {"event": "error", "message"} on stdout, after the report
   of the properties already checked (see lib/machine.elpi) *)
let report_stop ~json messages =
  List.iter prerr_endline messages;
  if json then begin
    let message = String.concat "\n" messages in
    print_endline (Yojson.Safe.to_string (`Assoc [ ("event", `String "error"); ("message", `String message) ]))
  end

(* -- Running ------------------------------------------------------------- *)

let run o file =
  let file = if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file in
  let dir = temporary_directory () in
  at_exit (fun () -> try remove_directory dir with Sys_error _ -> ());
  (* the checker's files, then the facts of the program *)
  List.iter (fun (name, text) -> write (Filename.concat dir name) text) Embedded.files;
  let paths = dir :: o.paths in
  let facts =
    try Elpi_reflect.Reflect.reflect_files ~paths ~defines:o.defines ~builtins:true ~closed:true [ file ]
    with Elpi_reflect.Reflect.Error msg -> raise (Stop [ msg ])
  in
  let facts_file = Filename.concat dir "program.reflect.elpi" in
  write facts_file facts;
  let driver_file = Filename.concat dir "driver.elpi" in
  write driver_file (driver ~program:file ~facts:facts_file);
  (* compile *)
  let flags = { API.Compile.default_flags with
                defined_variables = API.Compile.StrSet.of_list o.defines; max_errors = 10 } in
  let elpi = API.Setup.init ~flags:(API.Compile.to_setup_flags flags)
      ~builtins:[ Builtin.std_builtins ]
      ~file_resolver:(API.Parse.std_resolver ~cwd:dir ~paths ()) () in
  let show_warnings ws =
    if o.verbose then List.iter (fun (w : API.Error.warning) -> Format.eprintf "%a@." API.Error.pp w.warning) ws
  in
  let ast, errors, warnings =
    try API.Parse.program ~flags ~elpi driver_file
    with API.Parse.ParseError (loc, msg) -> raise (Stop [ Format.asprintf "%a: %s" API.Ast.Loc.pp loc msg ])
  in
  show_warnings warnings;
  if errors <> [] then fail_with_errors errors;
  let program, errors, warnings = API.Compile.program ~flags ~elpi ast in
  show_warnings warnings;
  if errors <> [] then fail_with_errors ~generated:facts_file errors;
  let args = String.concat ", " (List.map (Printf.sprintf "%S") o.checker_args) in
  let text = Printf.sprintf "check.main [%s]." args in
  let query =
    match API.Parse.query ~elpi ~loc:(API.Ast.Loc.initial "(elpi-check)") ~text with
    | Ok q, _ -> q
    | Error e, _ -> fail_with_errors [ e ]
  in
  let query = match API.Compile.query program query with Ok q, _ -> q | Error e, _ -> fail_with_errors [ e ] in
  let executable = API.Compile.optimize query in
  match API.Execute.once executable with
  | API.Execute.Success _ -> 0
  | API.Execute.Failure | API.Execute.NoMoreSteps -> 1

let () =
  let o, file = parse_options () in
  let code =
    try run o file with
    | Stop messages -> report_stop ~json:o.json messages; 2
    | API.Error.ElpiError e -> report_stop ~json:o.json [ error_text e ]; 2
  in
  exit code
