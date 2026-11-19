# elpi-debug: requested features of Elpi

This document lists the features of Elpi that would remove the workarounds
of elpi-debug, ordered by expected benefit.

elpi-debug ([`README.md`](README.md)) is a debugger for
standalone Elpi 4 written as a meta-interpreter in Elpi: it runs a goal
by interpreting the rules of the program, which
[`../reflect`](../reflect/README.md) gives as Elpi facts, and shows the
ports of each call, the unify steps with their bindings, `pi` and `=>`,
CHR at work, a failure explained; it has interactive stepping and drives
a debug adapter for VS Code ([`../dap`](../dap/README.md)).  Elpi is
version 4.0.0 or 4.1.1.  Checked against Elpi 4.1.1 (tag v4.1.1, commit
631d14a): none of the items below is provided by it (its new builtins are
the `std.fmt` boxes and the declaration of `=!=>`; its new API is about
packages, plugins and warnings), and item 7 is fixed after it.

Wherever the debugger works around something Elpi does not offer, the
workaround is a **stand-in** behind a small interface in one place, and
it is one item below.  Each item gives the API that would remove it (its
signature, in Elpi as in `builtin.elpi`, or in OCaml), its contract, where
elpi-debug would use it (file:predicate), what would go away (code, cost,
limits), and whether it is a bug fix or a feature.  The items are ordered
by what they would bring to the debugger.

| place | stand-ins | items |
|---|---|---|
| [`lib/primitives.elpi`](lib/primitives.elpi) | the variables of a term, their identity and printing, the trail, the shape of a term, the scope of a variable | 1, 2, 3, 9, 11 |
| [`lib/chr-hooks.elpi`](lib/chr-hooks.elpi), [`bin/chr_in_view.ml`](bin/chr_in_view.ml) | CHR: the goals of the rules, their attempts, the identity of a suspension, the store | 4, 5, 6 |
| [`lib/program.elpi`](lib/program.elpi), section Bridges | the bridges as static rules | 7 |
| [`bin/elpi_debug_main.ml`](bin/elpi_debug_main.ml), `to_api` | the one `Obj.magic` | 8 |
| [`lib/stepper.elpi`](lib/stepper.elpi), section Unwinding | retry and fail | 10 |
| [`../reflect`](../reflect/README.md) | the rules of the program as data, their locations | 12, 14 |
| [`lib/compiled.elpi`](lib/compiled.elpi), [`lib/natives.elpi`](lib/natives.elpi) | the shape of the compiled clauses (a cost) | 13 |
| [`bin/elpi_debug_main.ml`](bin/elpi_debug_main.ml), `query_variables` | the names of the query variables | 15 |

**Running the tests.**

```sh
opam install elpi.4.1.1 yojson dune    # or elpi.4.0.0, in any opam switch
cd elpi-tools
dune build @runtest                    # all the tests: debug, reflect, check, dap
dune exec -- elpi-debug -trace debug/tests/append.elpi 'rev [1,2] R'
dune exec -- elpi-debug -i debug/tests/lambda.elpi 'of (lam x\ lam y\ x) T'
```

The tests of the debugger are the cram files `tests/*.t` (`dune promote`
accepts a new output); `tests/bench.elpi` and `tests/chrbench.elpi` are
benchmarks, not run by the tests.

---

## 1. `vars-of`: the variables of a term (feature)

```elpi
% [vars-of T Vs] Vs are the unification variables occurring in T, each
% once, in the order of their first occurrence (left to right, depth
% first), under binders and inside applications of builtins.  An applied
% variable (X a b) is given by its head X.  Binds nothing.
builtin func vars-of any -> list any.
```

**Used by** `primitives.elpi:trail-mark` (the variables in reach, until
item 3), `primitives.elpi:hyps-vars` (those of the hypothetical clauses
in scope), `lprolog.elpi:show-scope` (command `scope`),
`lprolog.elpi:mentions-var` (the occurs check in
`explain.elpi:flex-clash`), `machine.elpi:frame-json` (the variables of
each goal for the debug adapter); and `compiled.elpi:compile-rules`,
which would close the rules itself (below).

**It removes** the walk of `primitives.elpi:vars-acc` over `shape-of`,
and its blind spots: the variables inside an application of a builtin
(`X is Y + 1` is one node that Elpi code cannot take apart) and inside a
conjunction of more than 16 goals (one pattern per arity, item 9).
Because of the first, the debugger cannot close a rule of the program
itself, so elpi-reflect prints each rule a second time, closed (option
`-closed`, the fact `reflect.closed-clause N F`,
`../reflect/lib/reflect.ml:rule_fact`), for `compiled.elpi:compile-rules`,
and the drivers ask for it (`bin/elpi_debug_main.ml:interpreted_units`,
`~closed:true`; also `../check/bin/elpi_check_main.ml`).  With `vars-of`,
the debugger would fetch `reflect.clause`, abstract its n variables (bind
them to the eigenvariables of `pi x1..xn\`), and `-closed` would go.  It
also removes a renaming: the walk gets the head of an applied variable
with the builtin `var`, which, on a variable kept in Elpi's compact form
(`G x`, printed `X0^1`), binds it to a new variable, so the same variable
shows under two numbers (`tests/interactive.t`).

## 2. `uuid`: the identity of a variable, and a printer that uses it (feature)

```elpi
% [uuid X N] N identifies the unification variable X for the whole run:
% different variables have different numbers, a variable keeps its number
% at every event and across backtracking.  Fails if X is not a variable;
% a variable bound to another one has the number of that one.
builtin func uuid any -> int.

% [term_to_string_named T Names S] S is T printed on one line, each
% unification variable as X<uuid>, each eigenvariable E of a pair
% (pr E Name) of Names as Name, the others as Elpi prints them (c<level>).
builtin func term_to_string_named any, list (pair any string) -> string.
```

**Used by** `primitives.elpi:uuid-name` and `show-term` (every printed
term: traces, explanations, the JSON of `-machine`),
`primitives.elpi:snapshot-of` and `bound-since` (the stand-in of the
trail, until item 3), `machine.elpi:var-scope-json` and `binding-json`.

**It removes** `primitives.elpi:printer-number`, `plain-text` and
`rename-eigens`: the stand-in reads the number Elpi's printer gives a
variable at its first print (the only place where Elpi code sees a
variable's identity), which costs a print per name and is wrong inside a
copy (`std.findall` prints its copy with a table of its own, from `X0`:
the debugger names no variable there); then it edits the printer's text
with regular expressions: the depth suffix dropped (`X12^1` is `X12`), the
line breaks of long terms replaced by spaces, each eigenvariable
`c<level>` replaced by its source name (`x#3`).  A table kept in Elpi
cannot replace `uuid`: a safe refuses a term with variables, a local
clause does not outlive its goal, and `same_var` cannot tell a variable
from one bound to it.  The printer already has the line, commented out,
in `runtime.ml` (`"X" ^ string_of_int (uvar_id r)`).  Also seen in
elpi-dap: one variable printed under two names in two panels
(`../dap/README.md`, Limits).

## 3. The trail: `trail-mark` and `bindings-since` (feature)

```elpi
data trail-mark.
% [trail-mark M] M marks the current point of the trail.
builtin func trail-mark -> trail-mark.

data pruning.
symb not-pruned pruning.
symb pruned-arguments int -> int -> int -> pruning.  % replaced by the variable of uuid U applied to K of its N arguments
symb pruned-scope list any -> pruning.               % replaced by a variable that may no longer depend on these eigenvariables

data binding.
symb binding int -> any -> pruning -> binding.       % uuid, value now, pruning

% [bindings-since M Bs] the bindings made since M and still in force: one
% per variable that existed at M and is bound now (the variables created
% after M are parts of the values), in the order of the trail.
builtin func bindings-since trail-mark -> list binding.
```

(`debug-unif T1 T2 Bs`, mark, `T1 = T2`, bindings since, is not needed by
elpi-debug: its head unification is split between Elpi's own clause
selection and the goals of `compiled.elpi`.)

**Used by** `ports.elpi:unify-port` and `unify-mark` (the unify event:
mark, end of the head unification, bindings since),
`ports.elpi:mark-if-seen` and `exit-port-with-bindings` (mark at the call
port, the exit port shows what the whole call computed), and through
`made-bindings`, `machine.elpi:bindings-json` (the debug adapter's Goal
scope).  The interface is `primitives.elpi:trail-mark G M` (G, the goal
about to run, is for the stand-in only).

**It removes** the stand-in, a snapshot of the variables in reach
compared with what they are now (`primitives.elpi:snapshot-of`,
`bound-since`, `pruning-of`, `lambda-prefix`, which tests the scope of
each variable by trying to bind it to each eigenvariable in force), and
`primitives.elpi:in-reach` / `hyps-vars`, which find where the variables
a goal may bind are (its goal and the hypothetical clauses in scope).  It
would be exact (a variable reached only through the constraint store, or
inside an application of a builtin, is missed today) and its cost would
be the bindings made, not the size of the goal and of the hypotheses:
every call could take a mark, where today only the calls seen at their
call port do.

## 4. CHR: the goal of a rule run in the current program (feature)

```elpi
% A rule attribute (or a flag of the compiler): the new goal of the rule
% runs with the program of the constraint that triggered the rule (the
% program Elpi keeps with each suspended goal, for its resumption: the
% static rules and the local clauses in force at its declaration), not
% with the static program only.
constraint p q {
  :current-program
  rule (p X) \ (q X) <=> goal X.
}
```

Today (elpi 4.0.0 and 4.1.1, `runtime.ml:try_fire_rule`) the new goal of a rule is
made with `initial_program`, the static program.  For elpi-debug any
program of the run would do (the interpreter keeps its compiled rules,
options and state as local clauses of `run`, installed once at the start).

**Used by** `bin/chr_in_view.ml:requested_goal`, which would rewrite the
goal N of a rule as `debug.run-rule-goal Loc N` (`chr.elpi:run-rule-goal`)
directly.

**It removes** the runner (`chr-hooks.elpi`, section §4:
`hand-rule-goal`, `rule-goal-request`, `rule-runner`, its CHR rule,
`start-rule-runner`, `start-rule-runner-if-needed`, `own-constraint`, and
its call in `interpreter.elpi:run`): a goal suspended at the start of the
run, so with the program of `run`, to which the goal of a rule is handed
through CHR itself, since a rule's goal reaches nothing of the run but the
store.  With it goes a difference from the real engine (README, Limits):
the runner and its requests in the store (hidden by `store`, seen by
`print_constraints`).

## 5. CHR: an event on each attempt of a rule, and its outcome (feature)

```ocaml
(* in API.Setup.init, or settable on an executable *)
type chr_attempt = {
  rule_loc : Ast.Loc.t;                  (* the rule, at its first head *)
  rule_name : string option;
  kept : int list;                       (* the constraints matched, by identity (item 6) *)
  removed : int list;
  outcome : [ `Heads_do_not_match | `Guard_failed | `Fired ];
}
val on_chr_attempt : (chr_attempt -> unit) -> unit
```

Called in the order of the attempts, for each rule tried on a tuple of
constraints, after its guard (or after the matching of the heads, when
they do not match).  An Elpi-level form would do as well (a builtin that
takes the attempts since the last call, as data).

**Used by** `chr-hooks.elpi:take-rule-notes` (its clause would read the
attempts), `chr.elpi:show-rule-attempts` (the events "tried on [S1, S2]",
"fires, removes [S2]", "guard fails"; breakpoints on a CHR rule;
`machine.elpi:tried-rule-json`).

**It removes** the rewriting of every guard
(`bin/chr_in_view.ml:with_attempt_reported`: `rule-tried Loc Kept
Contexts, G, rule-guard-held`), the context variables named for it
(`with_named_contexts`), the queue of notes in the driver (OCaml builtins
`debug.builtin-note-rule`, `debug.builtin-take-rule-notes`, their clauses
`Chr_in_view.clauses`), and `chr-hooks.elpi:rule-tried`,
`rule-guard-held`, `note-declaration`, `note-rule`.  (A guard runs in a
runtime of its own with the static program only: that is why the notes
go through OCaml.)  A limit goes: the attempts whose heads do not match
are not shown today (Elpi filters them before the guard).

## 6. CHR: the identity of a suspended goal, and the store from Elpi (feature)

```elpi
% [declare_constraint_as N G Keys..] as declare_constraint G Keys.., the
% suspension carrying the number N (any int the caller chooses), kept
% with it, given back by constraints and by the attempts of item 5.
builtin func declare_constraint_as int, (func), any.. .

% [constraints Gs] the goals of the constraint store, most recent first,
% each with the number of its suspension (0 when declared without one); a
% goal suspended under more binders than here comes under as many λs.
builtin func constraints -> list (pair int any).
```

(In OCaml, the same number as a field of `API.RawData.suspended_goal`.)

**Used by** `natives.elpi:delay` and `suspension-clauses` (the delay port
names the suspension `[S2]`, and its resume port when it is woken),
`chr-hooks.elpi:context-suspension` (the numbers of the constraints of an
attempt), `chr-hooks.elpi:program-store` (command `store`,
`machine.elpi:store-json`).

**It removes** `chr-hooks.elpi:suspended-as` (a local clause installed
around `declare_constraint`, so that the context of the constraint holds
its number), the rewriting of every constraint block
(`bin/chr_in_view.ml:constraint_block`, `debug.suspended-as` added to its
context filter), the reading of the number in the context
(`chr_in_view.ml:suspension_number`), and the driver's builtin for the
store (`chr_in_view.ml:store_contents`, `debug.builtin-store`;
`chr-hooks.elpi:constraint-store`, `store-readable`).  A difference from
the real engine goes: the context of a constraint holds
`debug.suspended-as K` (seen by `print_constraints` and by a rule that
names the context of a constraint, `(C ?- p X)`).

## 7. LPCIC/elpi#505: a crash with CHR and a `pi` local clause (bug fix)

A CHR rule firing on a constraint whose predicate has a `pi`-quantified
local clause in scope stops Elpi with `Invalid_argument("index out of
bounds")` (elpi 4.0.0 and 4.1.1, commit 631d14a).  Minimal form:
[`tests/elpi-bugs/chr-pi-local-clause.elpi`](tests/elpi-bugs/chr-pi-local-clause.elpi)
(`elpi -test chr-pi-local-clause.elpi`).

**Status:** fixed on Elpi's master (b5dec85, 2026-11-19), after Elpi
4.1.1, which still crashes.  The stand-in below stays while elpi-tools
supports a release without the fix.

**Used by** `program.elpi`, section Bridges (one native rule per
predicate of the program, `P X1 .. Xn :- !, debug.bridge (P X1 .. Xn)`,
which sends a native call back to the interpreter): `interpreter.elpi:run`
would install the bridges as local clauses `pi x1..xn\ ...`, with the
compiled rules.

**It removes** `program.elpi:write-bridges`, `write-bridge` and
`bridge-text`, and in the driver (`bin/elpi_debug_main.ml:interpreted_units`)
the first compilation and run of the program that writes them, the
temporary file and the fifth compilation unit: one compilation less at
each start.

## 8. API: compile a program built from parsed units (feature, small)

```ocaml
(* the parser's program as the API's: the identity today *)
val API.Ast.program_of_parsed : Elpi_parser.Ast.Program.t -> API.Ast.program
(* or: API.Compile.program taking several parsed units *)
```

The debugger compiles FILE **without its rules** (they are given to the
interpreter as data, and Elpi must not run them), together with the
interpreter, the rules as facts and the bridges.  It parses FILE with the
parser library, whose type it sees, removes the rules, rewrites its CHR
rules (items 4-6), and must compile the result with other units; the
API's parsed program is abstract.

**Used by** `bin/elpi_debug_main.ml:to_api`, called by `compile`.

**It removes** the one `Obj.magic` of the driver.  It is the identity in
elpi 4.0.0 and 4.1.1 (`type program = Ast.Program.t` in `API.ml`), but nothing
checks it: a later Elpi that changes that type would compile and then
crash at run time.  The README (Limits) has a minimal example.

## 9. Taking a goal apart: conjunctions, builtins, λ-terms (feature)

```elpi
% [conjuncts G Gs] G is a conjunction (A1, .., An), n >= 2, as Elpi
% represents it (one node), and Gs = [A1, .., An]; fails otherwise.
builtin func conjuncts (pred) -> list (pred).

% [builtin_app T Head Args] T is an application of a builtin predicate
% or connective (, ; => :- = pi sigma ! declare_constraint pattern_match
% findall_solutions, or one written in OCaml: var, is, print...), Head
% a term naming it, Args its arguments; with T unbound and Head, Args
% given, it builds the application.  Fails on any other term.
builtin func builtin_app any -> any, list any.

% [is_lambda T] T is a λ-abstraction x\ ... (T is not eta-expanded).
builtin func is_lambda any.
```

**Used by** `primitives.elpi:conjuncts` (`interpreter.elpi:compile`,
`connective`, `compiled.elpi:compile-body`), `primitives.elpi:shape-of`
(`vars-of`, `lprolog.elpi:binder-count`, `explain.elpi:subterm-clash`),
`primitives.elpi:is-lambda`; and elpi-check's own copy,
`../check/lib/goals.elpi:conjuncts`.

**It removes** one pattern of `conjuncts` per arity up to 16 (a
conjunction of more than 16 goals at one level is not taken apart: a
limit of the debugger, of elpi-check and of elpi-dap), the patterns of
`shape-of` for each connective, the blind spot of `vars-of` in an
application of a builtin (`shape-of _ leaf`), and `is-lambda`, which
tells a λ-term by its printed text (`"c0 \ ..."`, a print per test).
Building a conjunction needs nothing new: `(G, C)` nested runs the same.

## 10. Backtrack to a recorded point: `catch` and `throw` (feature, core)

```elpi
% [catch G Ball H] runs G.  If [throw B] is called while G runs (inside
% any goal, not, std.findall...), B a closed term that unifies with a copy
% of Ball: the bindings made since catch was called are undone, the
% choice points created since are dropped, Ball is unified with B, and H
% runs in place of G.  Otherwise catch G Ball H is G.
builtin func catch (pred), any, (pred).
% [throw B] unwinds to the innermost catch whose Ball unifies with B.
builtin func throw any.
```

As in ISO Prolog.  It touches the core of Elpi's machine, not only its
data.

**Used by** `interpreter.elpi:attempt` (the choice point before the call
port of each call: it would catch the request about that call) and
`stepper.elpi`, section Unwinding: `unwind-for` would throw the request
(retry `r`, fail `f`, `r N` for a call of the stack; elpi-dap's
restartFrame).

**It removes** the unwinding by failure: today the request is recorded
in a safe and every event fails at once (`stepper.elpi:unwinding`, tested
at each event by `ports.elpi:event-seen` and `native-port`) until the
choice point of the call (`unwound-to`).  Retry would be immediate, and
would no longer backtrack into every choice point left inside the call,
running again the builtins with several solutions met on the way.
(Undoing the trail to a mark, item 3, is not enough: the choice points
created since would remain.)

## 11. The scope of a variable (feature, small)

```elpi
% [scope_of V Es] Es are the eigenvariables in scope that the
% unification variable V may depend on, oldest first.
builtin func scope_of any -> list any.
```

**Used by** `primitives.elpi:visible-eigens` (`snapshot-of` and
`pruning-of`: the pruning of a scope at a unify step;
`lprolog.elpi:show-var-scope`, command `scope`;
`machine.elpi:var-scope-json`), `primitives.elpi:can-depend`
(`explain.elpi:out-of-scope`, "X cannot depend on the eigenvariable
x#3").

**It removes** `can-depend` and `keep-visible`, which try the binding
`V = E` for each eigenvariable E in scope and undo it (Elpi refuses it
when E is younger than V): one unification per eigenvariable, at each
snapshot of the trail (until item 3) and each scope shown.

## 12. The rules of the program as data (feature, large)

```ocaml
(* the rules of a compiled program, as Elpi terms, after scoping
   (namespace, shorten), macros, spilling and the order of :before,
   :after, :replace, :remove; with their location, attributes and the
   source names of their binders *)
val API.Compile.rules : program -> (rule_info * API.Data.term) list
```

or in Elpi, Prolog's `clause/2` (`builtin func rules any -> list (pred)`,
the rules of a predicate).

**Used by** `../reflect` (elpi-reflect), whose facts the debugger reads
in `program.elpi:program-rule`, `numbered-rules`, `clause-location`,
`declarations`, `compiled.elpi:compile-rules` and `machine.elpi` (the
listing for the adapter).

**It removes** elpi-reflect's own copy of the compiler's front end: the
name resolution of namespaces and `shorten` (`../reflect/lib/scope.ml`,
246 lines), the desugaring of spilling (`../reflect/lib/spill.ml`, 98
lines), the order of the rules (`reflect.ml:place_rules`), and their
limits (`../reflect/README.md`, "Not supported": rules using a macro, a
spill under a λ inside an atom or in a hypothesis, `:autospill`).  The
facts would then be made from what Elpi compiles, not from a second
reading of the source.

## 13. `:nooc` for local clauses (feature, a cost)

Elpi makes the occurs check on the head unification of every local
(hypothetical) clause; `:nooc` does not apply to them.  Wanted: `:nooc`
honoured for the local clauses of a predicate declared so.

**Used by** `compiled.elpi:compiled` (the compiled clauses of the
program, installed as local clauses by `run`) and `natives.elpi:run-native`
(the local clause `current-ctx Entry Ctx`).

**It removes** a constraint on the design rather than code: a compiled
clause must do all its work in its body and return nothing, since a
binding made by its head walks the term bound (a first version that
returned the compiled body was quadratic, `count 6400` 4.5 s; README,
Cost); and reading back `current-ctx` at each call back walks the whole
stack of frames.

## 14. Locations: the end line, and where a CHR rule starts (feature; a bug?)

- A location (`Ast.Loc.t`) gives the start (line, column) and the offset
  of the end of a term, not the line of its end.  Wanted: the end line
  and column too.
- A CHR rule without attributes has a location that starts at the end of
  the token before it (the `{` of its block or the dot of the rule
  before), often the line above.  Wanted: the location of the rule at its
  first head.

**Used by** `../reflect/lib/reflect.ml:end_position` (the places of the
premises of a rule, `reflect.premises`, for the premise of each call and
the breakpoints of elpi-dap) and `reflect.ml:chr_rule_loc`.

**It removes** the second reading of each source file to find the end
line, and its fallback when the file cannot be read (Elpi's resolver may
name a file by a path that does not exist: seen in dune's test sandbox,
cause not known), wrong by a line when a closing parenthesis stands on a
line of its own; and the search for the first head of a CHR rule.

## 15. The names of the variables of a query (feature, small)

```ocaml
(* the source names of the variables of a query, in the order of their
   first occurrence, as in the assignments of a solution *)
val API.Compile.query_variables : query -> string list
```

**Used by** `bin/elpi_debug_main.ml:query_variables` (the option
`debug.query-vars`: at each stop of `-machine`, the variables of the query
by their source names, the Query scope of elpi-dap).

**It removes** a second parse of the goal and a walk that decides, as the
compiler does, which names are variables (a capital letter, not bound by
a λ of the goal).

## 16. The documentation of `names` (bug fix, documentation)

`builtin.elpi` says that `names` gives the eigenvariables "in order of
age (young first)"; its code (`builtin.ml`, `list_init 0 depth`) gives
the oldest first, `c0` first.  elpi-debug relies on the code
(`primitives.elpi:rename-eigens`).

---

**Not a workaround** (seen while making this list): the pause of a front
end (elpi-dap sends SIGUSR1, and the interpreter asks the driver's
builtin `debug.signal-received` at each event) is the debugger's own
business: an interpreter that looks at every event can stop at any of
them.
