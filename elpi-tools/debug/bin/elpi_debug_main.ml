(* elpi-debug [OPTION].. FILE GOAL

   Runs GOAL on the Elpi program FILE through the meta-interpreter
   debug.elpi (see ../README.md), or with the real engine (-native), or
   both, comparing their answers (-compare).

   The interpreted program is made of six compilation units, in order:
   1. reflect.elpi, the format of a reflected program (../../reflect);
   2. debug.elpi, the interpreter;
   3. FILE without its rules: its declarations and CHR rules, so that the
      terms of the program type check and CHR runs natively (the CHR
      rules rewritten, so that the interpreter sees them at work: "CHR in
      view" below);
   4. the rules of FILE as reflect facts, printed by elpi-reflect;
   5. the bridges: one native rule per predicate of FILE, which sends a
      native call of that predicate back to the interpreter (written by
      debug.write-bridges, run on units 1-4);
   6. the clauses that tie the interpreter to the builtins of this driver:
      whether a front end asked for a pause (-machine), the notes of the
      CHR rules, the constraint store. *)

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
let machine = ref false            (* -machine: a front end drives the session *)
let args = ref []
let rule_events = ref false        (* the CHR rules report their attempts (see "CHR in view") *)

let add_option o = elpi_options := !elpi_options @ [ o ]

(* [add_event_option o]: an option that shows events, the attempts of the
   CHR rules among them *)
let add_event_option o = rule_events := true; add_option o

let usage =
  "elpi-debug [OPTION].. FILE GOAL\n\
   Runs GOAL (an Elpi goal, in quotes) on the program FILE through the debugger.\n\
   Options:"

let spec =
  Arg.align
    [
      ("-trace", Arg.Unit (fun () -> add_event_option "debug.trace"), " show the ports of every call");
      ("-builtins", Arg.Unit (fun () -> add_event_option "debug.builtins"), " also show the calls to builtins");
      ( "-break",
        Arg.String (fun p -> add_event_option (Printf.sprintf "debug.break %S" p)),
        "PRED stop at each call of PRED (repeatable)" );
      ("-i", Arg.Unit (fun () -> add_event_option "debug.interactive"), " interactive stepping: stop at each event, read commands from stdin");
      ("-echo", Arg.Unit (fun () -> add_option "debug.echo"), " print each command read (for scripted sessions)");
      ( "-machine",
        Arg.Unit (fun () -> add_event_option "debug.interactive"; add_option "debug.machine"; machine := true),
        " interactive stepping for a front end: a machine-readable line at each stop (see lib/machine.elpi)" );
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

(* ---- Pause, for a front end (-machine) ------------------------------------ *)

(* A front end asks for a pause by sending the signal SIGUSR1 to elpi-debug
   while the goal runs: the interpreter stops at the next event (it asks
   debug.pause-requested at each event, see ../lib/machine.elpi). *)
let pause_asked = ref false

let listen_for_pause () = Sys.set_signal Sys.sigusr1 (Sys.Signal_handle (fun _ -> pause_asked := true))

(* ---- CHR in view: the notes of the rules, the store ------------------------ *)

(* The notes that the CHR rules of FILE make while Elpi tries them (a rule
   tried on some constraints, its guard held: ../lib/chr.elpi), in order,
   most recent first, until the interpreter takes them.  A guard runs in a
   runtime of its own, with the static program only (elpi 4.0.0,
   runtime.ml, try_fire_rule): the local clauses of the interpreter are out
   of its reach, a queue of this driver is not.  The notes are closed
   terms, copied as a safe copies them. *)
let rule_notes : API.Data.term list ref = ref []

(* [suspension_number hyps]: K when the hypothesis debug.suspended-as K is
   among hyps, the context of a suspended goal (the interpreter numbers its
   suspensions so: ../lib/natives.elpi, [delay]); 0 otherwise. *)
let suspension_number (hyps : API.RawData.hyps) =
  let open API.RawData in
  let number_in { hdepth; hsrc } =
    match look ~depth:hdepth hsrc with
    | App (c, arg, []) when Constants.show c = "debug.suspended-as" -> (
        match look ~depth:hdepth arg with
        | CData d when API.RawOpaqueData.is_int d -> Some (API.RawOpaqueData.to_int d)
        | _ -> None)
    | _ -> None
  in
  Option.value ~default:0 (List.find_map number_in hyps)

(* [store_contents ~depth suspended]: the goals in the store, each with
   its suspension number, as terms at [depth]; a goal suspended under more
   binders than [depth] (inside a pi now left) comes under as many λs,
   which bind its eigenvariables out of scope here. *)
let store_contents ~depth suspended =
  let open API.RawData in
  let rec under_lambdas n t = if n <= 0 then t else under_lambdas (n - 1) (mkLam t) in
  List.map
    (fun { context; goal = goal_depth, goal; _ } -> (suspension_number context, under_lambdas (goal_depth - depth) goal))
    (API.RawData.constraints suspended)

(* [driver_builtins]: the builtins of this driver: the pause of a front
   end, the notes of the CHR rules and the store. *)
let driver_builtins =
  let open API.BuiltIn in
  let open API.BuiltInPredicate in
  let open API.BuiltInPredicate.Notation in
  let open API.BuiltInData in
  let signal_received ~depth:_ = if !pause_asked then pause_asked := false else raise No_clause in
  let note_rule (note, _) ~depth:_ = rule_notes := note :: !rule_notes in
  let take_rule_notes _ ~depth:_ =
    let notes = List.rev_map (fun n -> (n, 0)) !rule_notes in
    rule_notes := [];
    !:notes
  in
  let store _ ~depth _ constraints _ = !:(store_contents ~depth constraints) in
  declare ~file_name:"elpi-debug-driver.elpi"
    [ MLCode (Pred ("debug.signal-received", Easy "a pause was asked (signal SIGUSR1) since the last success", signal_received), DocAbove);
      MLCode (Pred ("debug.builtin-note-rule", In (closed "A", "Note", Easy "keeps a note of a CHR rule"), note_rule), DocAbove);
      MLCode
        ( Pred ("debug.builtin-take-rule-notes", Out (list (closed "A"), "Notes", Easy "the notes kept since the last call, oldest first"), take_rule_notes),
          DocAbove );
      MLCode
        ( Pred
            ( "debug.builtin-store",
              Out (list (Builtin.pair int any), "Goals", Read (API.ContextualConversion.raw_ctx, "the suspended goals, with their numbers")),
              store ),
          DocAbove ) ]

(* [driver_clauses]: the clauses that tie the interpreter to these
   builtins (the interpreter declares the predicates, with no clause:
   ../lib/machine.elpi, ../lib/chr.elpi). *)
let driver_clauses =
  String.concat "\n"
    [ "debug.pause-requested :- debug.signal-received.";
      "debug.note-rule N :- debug.builtin-note-rule N.";
      "debug.take-rule-notes Ns :- debug.builtin-take-rule-notes Ns.";
      "debug.constraint-store Gs :- debug.builtin-store Gs.";
      "" ]

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
    API.Setup.init ~builtins:[ Builtin.std_builtins; driver_builtins ]
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

(* ---- CHR in view: the CHR rules of FILE, rewritten ------------------------ *)
(* The CHR rules run natively (CHR at depth 1), rewritten so that the
   interpreter sees them at work (../lib/chr.elpi):
   - the goal N of a rule (rule ... <=> N) becomes
     [debug.hand-rule-goal Loc N]: N is run by the interpreter, not
     natively (natively, N would run with the static program only, where
     the interpreter's local clauses, and so the bridges, are missing);
   - with an option that shows events, the guard G of a rule (G is true
     when the rule has none) becomes
       debug.rule-tried Loc Kept [C1, ..., Cn], G, debug.rule-guard-held
     where Ci is the context of the i-th constraint matched (a variable
     in place of the context the rule does not read), Kept the number of
     constraints it keeps (those before \): the attempt, then the outcome
     of the guard, noted for the interpreter;
   - each constraint block gets debug.suspended-as in its context filter
     (constraint debug.suspended-as ... ?- ...), so that the context of a
     constraint holds the number the interpreter gave its suspension.
   Loc is the location of the rule, as reflect gives it (reflect.srcloc).
   Nothing else changes: the new guard step reads its arguments and binds
   none of the variables of the rule (Elpi freezes them during the guard
   anyway), declares no constraint, and always succeeds. *)

module T = PAst.Term

let named loc name = T.mkCon loc name
let string_term loc s = T.mkC loc (PAst.cstring.Elpi_util.Util.CData.cin s)
let int_term loc n = T.mkC loc (PAst.cint.Elpi_util.Util.CData.cin n)
let list_term loc ts = T.mkSeq ~loc (ts @ [ T.mkNil loc ])

(* [rule_location r]: the term reflect.srcloc File Line Column of the rule r,
   as reflect gives it (at its first head) *)
let rule_location (r : _ PAst.Chr.t) =
  let l = Elpi_reflect.Reflect.chr_rule_loc r in
  T.mkApp l
    [ named l "reflect.srcloc"; string_term l l.source_name; int_term l l.line; int_term l (l.source_start - l.line_starts_at) ]

(* [is_discarded t]: t is the context of a constraint that the rule does not read *)
let is_discarded (t : T.t) = match t.it with T.Const f -> PAst.Func.equal f PAst.Func.dummyname | _ -> false

(* [with_named_contexts ~first sequents]: the sequents of the constraints
   matched, with a variable of its own for each context the rule does not
   read (Debug_context_N, N from [first]), and the contexts (named or
   written by the rule), in order. *)
let with_named_contexts ~first (sequents : T.t PAst.Chr.sequent list) =
  List.split
    (List.mapi
       (fun i (s : T.t PAst.Chr.sequent) ->
         if is_discarded s.context then
           let context = named s.context.loc (Printf.sprintf "Debug_context_%d" (first + i)) in
           ({ s with context }, context)
         else (s, s.context))
       sequents)

(* [requested_goal r]: the goal of the rule r, run by the interpreter *)
let requested_goal (r : _ PAst.Chr.t) =
  Option.map
    (fun (s : T.t PAst.Chr.sequent) ->
      let l = s.conclusion.loc in
      { s with conclusion = T.mkApp l [ named l "debug.hand-rule-goal"; rule_location r; s.conclusion ] })
    r.new_goal

(* [with_attempt_reported r]: the rule r, whose guard notes its attempt and
   outcome first *)
let with_attempt_reported (r : _ PAst.Chr.t) =
  let l = r.loc in
  let to_match, kept_contexts = with_named_contexts ~first:1 r.to_match in
  let to_remove, removed_contexts = with_named_contexts ~first:(1 + List.length r.to_match) r.to_remove in
  let tried =
    T.mkApp l
      [ named l "debug.rule-tried"; rule_location r; int_term l (List.length r.to_match);
        list_term l (kept_contexts @ removed_contexts) ] in
  let guard = Option.to_list r.guard in
  let steps = (tried :: guard) @ [ named l "debug.rule-guard-held" ] in
  { r with to_match; to_remove; guard = Some (T.mkAppF l (l, PAst.Func.andf) steps) }

(* [in_view r]: the CHR rule r, rewritten as above *)
let in_view (r : _ PAst.Chr.t) =
  let r = { r with new_goal = requested_goal r } in
  if !rule_events then with_attempt_reported r else r

(* [with_suspension_numbers loc filter clique]: the constraint block, its
   context filter with debug.suspended-as *)
let with_suspension_numbers loc filter clique =
  PAst.Program.Constraint (loc, filter @ [ PAst.Func.from_string "debug.suspended-as" ], clique)

(* [without_rules p]: the program p (and the files it accumulates) without
   its rules; they are given to the interpreter as reflect facts instead.
   Its CHR rules are kept, in view. *)
let rec without_rules (p : PAst.Program.t) : PAst.Program.t =
  let rec decls = function
    | [] -> []
    | PAst.Program.Clause _ :: ds -> decls ds
    | PAst.Program.Chr r :: ds -> PAst.Program.Chr (in_view r) :: decls ds
    | PAst.Program.Constraint (loc, filter, clique) :: ds -> with_suspension_numbers loc filter clique :: decls ds
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
    try Elpi_reflect.Reflect.reflect_files ~paths:!paths ~closed:true [ file ]
    with Elpi_reflect.Reflect.Error msg -> fail "%s" msg
  in
  let first =
    [ parse_text "reflect.elpi" (Embedded.file "reflect.elpi"); parse_text "debug.elpi" (Embedded.file "debug.elpi");
      without_rules (parse_file file); parse_text "(facts)" facts ]
  in
  let bridges_file = Filename.temp_file "elpi-debug-bridges" ".elpi" in
  let exe = compile ~elpi ~flags first (Printf.sprintf "debug.write-bridges %S." bridges_file) in
  (match API.Execute.once exe with
   | API.Execute.Success _ -> ()
   | _ -> fail "could not write the bridges");
  let bridges = In_channel.with_open_text bridges_file In_channel.input_all in
  Sys.remove bridges_file;
  first @ [ parse_text "(bridges)" bridges; parse_text "(driver)" driver_clauses ]

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

(* [query_variables goal]: the source names of the variables of the query,
   in the order of their first occurrence (the names of "Solution: X =
   ..."): the names that start with a capital letter and are not bound by
   a λ of the goal; none if the goal does not parse (its compilation then
   reports the error). *)
let query_variables goal =
  let module T = PAst.Term in
  let found = ref [] in
  let rec walk bound (t : T.t) =
    match t.it with
    | T.Const f ->
        let name = PAst.Func.show f in
        if PAst.Func.is_uvar_name f && not (List.mem name bound || List.mem name !found) then found := name :: !found
    | T.App (head, args) -> walk bound head; List.iter (walk bound) args
    | T.Lam (x, _, _, body) -> walk (PAst.Func.show x :: bound) body
    | T.Cast (t, _) | T.Parens t -> walk bound t
    | T.CData _ | T.Quoted _ -> ()
  in
  let (module P : Parser) = parser () in
  (try walk [] (P.goal ~loc:(Elpi_util.Util.Loc.initial "(goal)") ~text:goal) with _ -> ());
  List.rev !found

(* [query_vars_option goal]: the option debug.query-vars of the variables
   of the query, by their source names (shown at each stop of -machine). *)
let query_vars_option goal =
  let pair name = Printf.sprintf "pr %S %s" name name in
  Printf.sprintf "debug.query-vars [%s]" (String.concat ", " (List.map pair (query_variables goal)))

let interpreted file goal ~limit ~print =
  let elpi, flags = setup ~det:false in
  let units = interpreted_units ~elpi ~flags file in
  let opts = String.concat ", " (!elpi_options @ [ query_vars_option goal ]) in
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
  if !machine then listen_for_pause ();
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
