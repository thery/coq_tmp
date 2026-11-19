(* CHR in view: the driver's side of the CHR hooks of elpi-debug
   (../lib/chr-hooks.elpi), STAND-INS for three features that Elpi's CHR
   engine lacks (../ELPI-FEATURE-REQUESTS.md):

   §4 the goal of a rule run in the current program, not the static one;
   §5 an event on each attempt of a rule and its outcome;
   §6 the identity of a suspended goal, and the store readable from Elpi.

   The CHR rules of FILE run natively (CHR at depth 1), rewritten so that
   the interpreter sees them at work:
   - the goal N of a rule (rule ... <=> N) becomes
     [debug.hand-rule-goal Loc N]: N is run by the interpreter, not
     natively (natively, N would run with the static program only, where
     the interpreter's local clauses, and so the bridges, are missing): §4;
   - with an option that shows events, the guard G of a rule (G is true
     when the rule has none) becomes
       debug.rule-tried Loc Kept [C1, ..., Cn], G, debug.rule-guard-held
     where Ci is the context of the i-th constraint matched (a variable
     in place of the context the rule does not read), Kept the number of
     constraints it keeps (those before \): the attempt, then the outcome
     of the guard, noted for the interpreter on a queue of this module
     ([note_rule], [take_rule_notes]): §5;
   - each constraint block gets debug.suspended-as in its context filter
     (constraint debug.suspended-as ... ?- ...), so that the context of a
     constraint holds the number the interpreter gave its suspension; the
     store is read by a builtin of this module ([store]), which gives that
     number with each goal: §6.
   Loc is the location of the rule, as reflect gives it (reflect.srcloc).
   Nothing else changes: the new guard steps read their arguments and bind
   none of the variables of the rule (Elpi freezes them during the guard
   anyway), declare no constraint, and always succeed. *)

open Elpi
module PAst = Elpi_parser.Ast
module T = PAst.Term

(* ---- The rules rewritten ------------------------------------------------ *)

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

(* [requested_goal r]: the goal of the rule r, run by the interpreter (§4) *)
let requested_goal (r : _ PAst.Chr.t) =
  Option.map
    (fun (s : T.t PAst.Chr.sequent) ->
      let l = s.conclusion.loc in
      { s with conclusion = T.mkApp l [ named l "debug.hand-rule-goal"; rule_location r; s.conclusion ] })
    r.new_goal

(* [with_attempt_reported r]: the rule r, whose guard notes its attempt and
   outcome first (§5) *)
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

(* [rule ~rule_events r]: the CHR rule r, rewritten as above; its attempts
   are reported when [rule_events] (an option shows events) *)
let rule ~rule_events (r : _ PAst.Chr.t) =
  let r = { r with new_goal = requested_goal r } in
  if rule_events then with_attempt_reported r else r

(* [constraint_block loc filter clique]: the constraint block, its context
   filter with debug.suspended-as (§6) *)
let constraint_block loc filter clique =
  PAst.Program.Constraint (loc, filter @ [ PAst.Func.from_string "debug.suspended-as" ], clique)

(* ---- The notes of the rules, the store ---------------------------------- *)

(* The notes that the CHR rules of FILE make while Elpi tries them (a rule
   tried on some constraints, its guard held: ../lib/chr-hooks.elpi), in
   order, most recent first, until the interpreter takes them.  A guard
   runs in a runtime of its own, with the static program only (elpi
   4.0.0 and 4.1.1, runtime.ml, try_fire_rule): the local clauses of the interpreter
   are out of its reach, a queue of this driver is not.  The notes are
   closed terms, copied as a safe copies them. *)
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

(* [builtins]: the builtins of CHR in view: the queue of the notes of the
   rules (§5) and the store (§6). *)
let builtins : API.BuiltIn.declaration list =
  let open API.BuiltInPredicate in
  let open API.BuiltInPredicate.Notation in
  let open API.BuiltInData in
  let note_rule (note, _) ~depth:_ = rule_notes := note :: !rule_notes in
  let take_rule_notes _ ~depth:_ =
    let notes = List.rev_map (fun n -> (n, 0)) !rule_notes in
    rule_notes := [];
    !:notes
  in
  let store _ ~depth _ constraints _ = !:(store_contents ~depth constraints) in
  [ MLCode (Pred ("debug.builtin-note-rule", In (closed "A", "Note", Easy "keeps a note of a CHR rule"), note_rule), DocAbove);
    MLCode
      ( Pred ("debug.builtin-take-rule-notes", Out (list (closed "A"), "Notes", Easy "the notes kept since the last call, oldest first"), take_rule_notes),
        DocAbove );
    MLCode
      ( Pred
          ( "debug.builtin-store",
            Out (list (Builtin.pair int any), "Goals", Read (API.ContextualConversion.raw_ctx, "the suspended goals, with their numbers")),
            store ),
        DocAbove ) ]

(* [clauses]: the clauses that tie the interpreter to these builtins (the
   interpreter declares the predicates, with no clause:
   ../lib/chr-hooks.elpi). *)
let clauses =
  [ "debug.note-rule N :- debug.builtin-note-rule N.";
    "debug.take-rule-notes Ns :- debug.builtin-take-rule-notes Ns.";
    "debug.constraint-store Gs :- debug.builtin-store Gs." ]
