(* elpi-debug [OPTION].. FILE GOAL

   Runs GOAL on the Elpi program FILE through the meta-interpreter
   debug.elpi (see ../README.md), or with the real engine (-native), or
   both, comparing their answers (-compare).

   The interpreted program is made of five compilation units, in order:
   1. reflect.elpi, the format of a reflected program (../../reflect);
   2. debug.elpi, the interpreter;
   3. FILE without its rules: its declarations and CHR rules, so that the
      terms of the program type check and CHR runs natively;
   4. the rules of FILE as reflect facts, printed by elpi-reflect;
   5. the bridges: one native rule per predicate of FILE, which sends a
      native call of that predicate back to the interpreter (written by
      debug.write-bridges, run on units 1-4). *)

open Elpi
module PAst = Elpi_parser.Ast

(* ---- Options ------------------------------------------------------------ *)

type mode = Interpreted | Native | Compare

let mode = ref Interpreted
let elpi_options = ref []          (* the options of debug.run, as Elpi terms *)
let all_solutions = ref false
let max_solutions = ref 100
let show_time = ref false
let show_warnings = ref false
let paths = ref []
let args = ref []

let add_option o = elpi_options := !elpi_options @ [ o ]

let usage =
  "elpi-debug [OPTION].. FILE GOAL\n\
   Runs GOAL (an Elpi goal, in quotes) on the program FILE through the debugger.\n\
   Options:"

let spec =
  Arg.align
    [
      ("-trace", Arg.Unit (fun () -> add_option "debug.trace"), " show the ports of every call");
      ("-builtins", Arg.Unit (fun () -> add_option "debug.builtins"), " also show the calls to builtins");
      ( "-break",
        Arg.String (fun p -> add_option (Printf.sprintf "debug.break %S" p)),
        "PRED stop at each call of PRED (repeatable)" );
      ("-i", Arg.Unit (fun () -> add_option "debug.interactive"), " interactive stepping: stop at each event, read commands from stdin");
      ("-echo", Arg.Unit (fun () -> add_option "debug.echo"), " print each command read (for scripted sessions)");
      ("-profile", Arg.Unit (fun () -> add_option "debug.profile"), " count ports and time per predicate");
      ("-no-explain", Arg.Unit (fun () -> add_option "debug.no-explain"), " do not explain a failure");
      ( "-random",
        Arg.Int (fun s -> add_option "debug.random-order"; add_option (Printf.sprintf "debug.seed %d" s)),
        "SEED try the candidate clauses in a random order (strategy for generation)" );
      ("-first", Arg.Unit (fun () -> add_option "debug.first-solution"), " keep the first solution of each call");
      ("-max-depth", Arg.Int (fun n -> add_option (Printf.sprintf "debug.max-depth %d" n)), "N calls deeper than N fail");
      ("-ignore-cut", Arg.Unit (fun () -> add_option "debug.ignore-cut"), " a cut does nothing");
      ("-all", Arg.Set all_solutions, " print all the solutions (default: the first)");
      ("-n", Arg.Set_int max_solutions, "N at most N solutions with -all or -compare (default 100)");
      ("-native", Arg.Unit (fun () -> mode := Native), " run with the real engine instead");
      ( "-compare",
        Arg.Unit (fun () -> mode := Compare),
        " run with both, compare all the answers (exit code 1 if they differ)" );
      ("-time", Arg.Set show_time, " print the execution time");
      ("-warnings", Arg.Set show_warnings, " print the compiler's warnings");
      ("-I", Arg.String (fun d -> paths := !paths @ [ d ]), "DIR search accumulated files in DIR");
    ]

(* ---- Elpi setup and errors ---------------------------------------------- *)

let fail fmt = Printf.ksprintf (fun s -> prerr_endline ("elpi-debug: " ^ s); exit 2) fmt

let report_errors errors =
  List.iter (fun (e : API.Error.t) -> Format.eprintf "@[<hv>Error: %a@]@." API.Error.pp e) errors

let report_warnings warnings =
  if !show_warnings then
    List.iter (fun { API.Error.warning = e; _ } -> Format.eprintf "@[<hv>Warning: %a@]@." API.Error.pp e) warnings

let or_exit (x, errors, warnings) =
  report_warnings warnings;
  if errors <> [] then (report_errors errors; exit 2);
  x

let query_or_exit (q, warnings) =
  report_warnings warnings;
  match q with Ok q -> q | Error e -> report_errors [ e ]; exit 2

let setup ~det =
  let flags = { API.Compile.default_flags with API.Compile.skip_det_checking = not det } in
  let elpi =
    API.Setup.init ~builtins:[ Builtin.std_builtins ]
      ~flags:(API.Compile.to_setup_flags flags)
      ~file_resolver:(API.Parse.std_resolver ~paths:!paths ())
      ()
  in
  (elpi, flags)

(* ---- Building the interpreted program ----------------------------------- *)

module type Parser = Elpi_parser.Parse.Parser_w_Internals

(* the parser, made once the options (the search paths) are known *)
let parser () : (module Parser) =
  let module P = Elpi_parser.Parse.Make (struct
    let versions = Elpi_util.Util.StrMap.empty
    let resolver = API.Parse.std_resolver ~paths:!paths ()
  end) in
  (module P : Parser)

(* [parse_or_fail read]: the program read by the parser, or its errors and exit *)
let parse_or_fail read : PAst.Program.t =
  let show (e : Elpi_util.Util.error) =
    (match e.loc with Some l -> Elpi_util.Util.Loc.show l ^ ": " | None -> "") ^ e.message in
  match read (parser ()) with
  | p, [], _ -> p
  | _, errors, _ -> fail "%s" (String.concat "\n" (List.map show errors))
  | exception Elpi_parser.Parse.ParseError (loc, msg) -> fail "%s: %s" (Elpi_util.Util.Loc.show loc) msg

(* [parse_text name text]: a unit from Elpi source text *)
let parse_text name text =
  let loc = Elpi_util.Util.Loc.initial name in
  parse_or_fail (fun (module P : Parser) -> P.program_from ~loc ~digest:(Digest.string text) (Lexing.from_string text))

(* [parse_file file]: a unit from a file, with the files it accumulates *)
let parse_file file = parse_or_fail (fun (module P : Parser) -> P.program file)

(* [without_rules p]: the program p (and the files it accumulates) without
   its rules; they are given to the interpreter as reflect facts instead. *)
let rec without_rules (p : PAst.Program.t) : PAst.Program.t =
  let rec decls = function
    | [] -> []
    | PAst.Program.Clause _ :: ds -> decls ds
    | PAst.Program.Accumulated (loc, ps) :: ds -> PAst.Program.Accumulated (loc, List.map without_rules ps) :: decls ds
    | d :: ds -> d :: decls ds
  in
  { p with ast = decls p.ast }

(* [program_of units]: one program accumulating the units in order *)
let program_of (units : PAst.Program.t list) : PAst.Program.t =
  let loc = Elpi_util.Util.Loc.initial "(elpi-debug)" in
  { PAst.file_name = "(elpi-debug)"; digest = Digest.string "elpi-debug"; deps = []; ast = [ PAst.Program.Accumulated (loc, units) ] }

(* [to_api p]: the parsed program p as the API's parsed program.  The one
   hack of the driver, isolated here: the API offers no way to compile a
   program built from parsed units (we need FILE without its rules), but
   its type of parsed programs is the parser's own: [type program =
   Ast.Program.t] in elpi 4.0.0's API.ml, so the conversion is the
   identity.  To check again with each new version of Elpi. *)
let to_api (p : PAst.Program.t) : API.Ast.program = Obj.magic p

let compile ~elpi ~flags units text =
  let prog = or_exit (API.Compile.program ~flags ~elpi (to_api (program_of units))) in
  let q = query_or_exit (API.Parse.query ~elpi ~loc:(API.Ast.Loc.initial "(goal)") ~text) in
  let q = query_or_exit (API.Compile.query prog q) in
  API.Compile.optimize q

(* [interpreted_units file]: the units 1-5 described at the top. *)
let interpreted_units ~elpi ~flags file =
  let facts =
    try Elpi_reflect.Reflect.reflect_files ~paths:!paths [ file ]
    with Elpi_reflect.Reflect.Error msg -> fail "%s" msg
  in
  let first =
    [ parse_text "reflect.elpi" Embedded.reflect_elpi; parse_text "debug.elpi" Embedded.debug_elpi;
      without_rules (parse_file file); parse_text "(facts)" facts ]
  in
  let bridges_file = Filename.temp_file "elpi-debug-bridges" ".elpi" in
  let exe = compile ~elpi ~flags first (Printf.sprintf "debug.write-bridges %S." bridges_file) in
  (match API.Execute.once exe with
   | API.Execute.Success _ -> ()
   | _ -> fail "could not write the bridges");
  let bridges = In_channel.with_open_text bridges_file In_channel.input_all in
  Sys.remove bridges_file;
  first @ [ parse_text "(bridges)" bridges ]

(* ---- Running ------------------------------------------------------------- *)

(* [one_line s]: s with its line breaks (Elpi's printer breaks long terms
   and λ-terms) replaced by spaces, as the tracer prints terms *)
let one_line s = Str.global_replace (Str.regexp "\n *") " " s

(* [solution_text]: the assignments of a solution, one "X = t" per line *)
let solution_text (s : API.Data.solution) =
  let b = Buffer.create 80 in
  API.Data.StrMap.iter
    (fun name v ->
      let value = one_line (Format.asprintf "%a" (API.Pp.term s.API.Data.pp_ctx) v) in
      Buffer.add_string b (Printf.sprintf "  %s = %s\n" name value))
    s.API.Data.assignments;
  Buffer.contents b

(* [run exe ~limit ~print]: the solutions of exe (at most limit), each
   printed as it is found when [print]; also the time taken. *)
let run exe ~limit ~print =
  let found = ref [] in
  let t0 = Unix.gettimeofday () in
  let pp _ = function
    | API.Execute.Success s ->
        let text = solution_text s in
        found := text :: !found;
        if print then Format.printf "Solution %d:\n%s%!" (List.length !found) text
    | API.Execute.Failure -> if print && !found = [] then Format.printf "No solution.\n%!"
    | API.Execute.NoMoreSteps -> Format.printf "Out of steps.\n%!"
  in
  let more () = List.length !found < limit in
  (try
     if limit = 1 then pp 0.0 (API.Execute.once exe)   (* no backtracking after the first *)
     else API.Execute.loop exe ~more ~pp
   with API.Error.ElpiError e -> report_errors [ e ]);
  Format.printf "%!";
  (List.rev !found, Unix.gettimeofday () -. t0)

(* [normalize s]: s with the unification variables X12, X3^1... renamed in
   order of appearance, so that answers of two runs can be compared. *)
let normalize s =
  let names = Hashtbl.create 7 in
  Str.global_substitute (Str.regexp "\\bX[0-9]+\\(\\^[0-9]+\\)?")
    (fun s ->
      let v = Str.matched_string s in
      match Hashtbl.find_opt names v with
      | Some n -> n
      | None -> let n = Printf.sprintf "_V%d" (Hashtbl.length names) in Hashtbl.add names v n; n)
    s

let interpreted file goal ~limit ~print =
  let elpi, flags = setup ~det:false in
  let units = interpreted_units ~elpi ~flags file in
  let opts = String.concat ", " !elpi_options in
  let exe = compile ~elpi ~flags units (Printf.sprintf "debug.run [%s] (%s)." opts goal) in
  run exe ~limit ~print

let native file goal ~limit ~print =
  let elpi, flags = setup ~det:true in
  let program =
    try or_exit (API.Parse.program ~flags ~elpi file)
    with API.Parse.ParseError (loc, msg) -> fail "%s: %s" (API.Ast.Loc.show loc) msg in
  let prog = or_exit (API.Compile.program ~flags ~elpi program) in
  let q = query_or_exit (API.Parse.query ~elpi ~loc:(API.Ast.Loc.initial "(goal)") ~text:(goal ^ ".")) in
  let exe = API.Compile.optimize (query_or_exit (API.Compile.query prog q)) in
  run exe ~limit ~print

let print_time what t = if !show_time then Format.printf "%s time: %.3f s\n%!" what t

let () =
  (* Elpi's own tracer, to debug the debugger: ELPI_DEBUG_TRACE="-trace-on ..." *)
  (match Sys.getenv_opt "ELPI_DEBUG_TRACE" with
   | Some s -> ignore (API.Setup.trace (String.split_on_char ' ' s))
   | None -> ());
  Arg.parse spec (fun a -> args := !args @ [ a ]) usage;
  let file, goal = match !args with [ f; g ] -> (f, g) | _ -> Arg.usage spec usage; exit 2 in
  if not (Sys.file_exists file) then fail "no file %s" file;
  paths := !paths @ [ Filename.dirname file ];
  let limit = if !all_solutions then !max_solutions else 1 in
  match !mode with
  | Interpreted ->
      let _, t = interpreted file goal ~limit ~print:true in
      print_time "interpreted" t
  | Native ->
      let _, t = native file goal ~limit ~print:true in
      print_time "native" t
  | Compare ->
      let n, tn = native file goal ~limit:!max_solutions ~print:false in
      add_option "debug.no-explain";
      let i, ti = interpreted file goal ~limit:!max_solutions ~print:false in
      print_time "native" tn;
      print_time "interpreted" ti;
      let n = List.map normalize n and i = List.map normalize i in
      if n = i then Format.printf "Same answers (%d).\n" (List.length n)
      else begin
        Format.printf "Different answers.\nNative (%d):\n%s\nInterpreted (%d):\n%s\n" (List.length n)
          (String.concat "--\n" n) (List.length i) (String.concat "--\n" i);
        exit 1
      end
