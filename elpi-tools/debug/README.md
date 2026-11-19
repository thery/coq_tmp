# elpi-debug: a debugger for standalone Elpi

A debugger for Elpi 4 programs (standalone Elpi, opam switch `elpi5`; not
Rocq-Elpi), written as a **meta-interpreter in Elpi**
([`lib/*.elpi`](lib), assembled into `debug.elpi`).  It runs a goal by interpreting the rules of
the program, which [`../reflect`](../reflect/README.md) gives as Elpi data,
and shows what the real engine does not:

- the four **ports** of each call (call, exit, redo, fail, as in Prolog
  tracers), and the steps of **λProlog** inside a call: the **unify** port
  of the selected clause (where it comes from, file:line or a hypothesis
  and the call that added it; the bindings it makes, higher-order ones and
  **pruning** included), the entry into **pi** (a new eigenvariable, shown
  with its source name, `x#3`, and its scope), the entry into **=>** (the
  clause added to the local program), the cut, and the **delay** of a goal
  by `declare_constraint` and its **resume** by CHR, numbered (`[S2]`);
- **interactive stepping** (`-i`), as in the box-model tracers of Prolog:
  creep, skip, leap, retry, fail, print, the scope of each logic variable,
  the local program, breakpoints set at the prompt;
- **breakpoints** on a predicate, with the calls above, the local program
  (and the call that added each clause) and the eigenvariables;
- **counts and time per predicate** (calls, exits, redos, fails, clauses
  tried, self time);
- on failure, an **explanation**: the deepest goal that failed at its first
  try, the calls above it, every clause tried and why it did not apply (the
  argument and the smallest subterms that clash, an input argument that the
  goal leaves unknown, the occurs check, a variable that cannot depend on an
  eigenvariable introduced after it), or that the predicate **has no
  clause at all** (in Elpi such a call just fails, silently).

## Usage

    elpi-debug [OPTION].. FILE GOAL

```
$ elpi-debug tests/undefined.elpi 'check [1,2]'
debug warning: positive has no clause at all (in the program or in the hypotheses in scope); its calls fail
debug: no (more) solution.
Deepest failure (depth 1): #2 positive 1
  called from:
    #1 check [1, 2]
  positive is declared but has no clause at all (in the program or in the hypotheses in scope)
No solution.

$ elpi-debug tests/append.elpi 'append [1] [2] [3]'
debug: no (more) solution.
Deepest failure (depth 0): #1 append [1] [2] [3]
  clauses tried:
    append.elpi:5: append [] X0 X0
        does not match: argument 1 (input): [1] vs []
    append.elpi:6: append [X1 | X2] X3 [X1 | X4]
        does not match: argument 3 (output): [3] vs [1 | X4], at 3 vs 1
No solution.

$ elpi-debug -trace tests/chr.elpi 'double 3 Y'
Call: #1 double 3 X0
Unify: #1 with chr.elpi:18: double 3 X0
  Call: #2 even X0
  Unify: #2 with chr.elpi:10: even X0
  Cut: #2 commits to its current clause
    Delay: [S1] even X0 on [X0]
  Exit: #2 even X0
    Resume: [S1] #3 even 6
    Unify: #3 with chr.elpi:10: even 6
    Unify: #3 with chr.elpi:11: even 6
    Exit: [S1] #3 even 6
Exit: #1 double 3 6
Solution 1:
  Y = 6
```

| option | |
|---|---|
| `-trace` | show the ports of every call |
| `-builtins` | also show the calls to builtins |
| `-break PRED` | stop at each call of PRED (repeatable); without `-i` the context is printed and the run goes on |
| `-i` | interactive stepping: stop at each event and read a command on stdin (below) |
| `-echo` | print each command read (for scripted sessions) |
| `-machine` | interactive stepping driven by a front end (the debug adapter [`../dap`](../dap/README.md)): a machine-readable line at each stop ([`lib/machine.elpi`](lib/machine.elpi)) |
| `-profile` | ports and self time per predicate |
| `-no-explain` | no explanation of a failure |
| `-all`, `-n N` | all the solutions (at most N), not only the first |
| `-native` | run the goal with the real engine instead |
| `-compare` | run with both, compare all the answers (exit code 1 if they differ) |
| `-random SEED`, `-first`, `-max-depth N`, `-ignore-cut` | the strategy (below) |
| `-time`, `-warnings`, `-I DIR` | |

`ELPI_DEBUG_TRACE="-trace-on tty stdout ..."` passes options to Elpi's own
tracer (to debug the debugger).

## Interactive stepping

With `-i` the interpreter stops at each event and reads a command after
the prompt ` ? ` (with `-break`, it first leaps to a breakpoint).  The
events are the ports of the calls (`Call`, `Exit`, `Redo`, `Fail`,
`Resume` for a woken goal) and the steps of λProlog (`Unify`, `Pi`,
`Assume`, `Delay`, `Cut`); `-trace` prints the same events without
stopping.  An excerpt of [`tests/interactive.t`](tests/interactive.t):

```
Call: #1 of (lam c0 \ lam c1 \ c0) X0
   ? c
Unify: #1 with lambda.elpi:14: of (lam c0 \ lam c1 \ c0) (arr X1 X2)
      X0 := arr X1 X2
   ? c
  Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of (lam c1 \ x#1) X2
   ? c
  Assume: of x#1 X1   (added to the local program, for of (lam c1 \ x#1) X2 only)
   ? c
  Call: #2 of (lam c1 \ x#1) X2
   ? scope
  eigenvariables in force (oldest first): x#1
    X2 may depend on: no eigenvariable
   ? hyps
  local program (clauses added by =>, most recent first):
    of x#1 X1    (hypothesis added by #1)
```

| command | |
|---|---|
| `c`, return | creep: go to the next event |
| `s` | skip: run this call to its exit or fail without stopping inside |
| `o` | out: run to the exit or fail of the call whose body runs this event (at a port of a call: the call above) |
| `l` | leap: run to the next breakpoint |
| `t` | trace: show every event, stop only at breakpoints |
| `n` | nodebug: run to the end (also at the end of stdin) |
| `r` | retry this call from its call port |
| `r N` | retry the call #N of the stack |
| `f` | make this call fail |
| `p` | print the goal, the local program and the scope |
| `g` | the calls above |
| `scope` | the eigenvariables in force and, for each logic variable of the goal, those it may depend on |
| `hyps` | the local program (the clauses added by `=>`, with the call that added each) |
| `+ P`, `- P` | set, remove a breakpoint on the predicate P |
| `+ clause N`, `- clause N` | set, remove a breakpoint on the clause numbered N in the listing of `-machine`: the run stops at the unify step of that clause |
| `e` | the deepest failure so far |
| `a` | abort |
| `h`, `?` | help |

A command acts on the focus of the event: the call whose port it is, or
whose body runs the pi, `=>` or cut.

**How retry and fail work.**  Each call is run by `attempt`, whose second
clause is a choice point placed just before the call port.  `r` (or `f`)
records the request "retry #N" (or "fail #N") in a safe, which survives
backtracking, and fails.  While a request is pending, every event fails at
once, so backtracking goes quickly through the choice points inside call
N, Elpi undoing their bindings as usual, and reaches the second clause of
`attempt` for N, which takes the request and runs call N again from its
call port, where it stops (or shows its fail port and fails); `r N` does
the same for any call #N of the stack.  The **local program and the
scope** are restored with the bindings: the clauses added by `=>` and the
eigenvariables of `pi` are Elpi's own (the interpreter keeps `=>` and `pi`
native), so going back to the choice point before the call port leaves
their scopes, as it undoes the bindings.  The cut does not get in the way:
a cut in a body is the native cut of `backchain`, which runs below
`attempt`, so it never removes the choice point of `attempt` of its own
call or of the calls above.  (A retried call gets new numbers for its
eigenvariables: they are new eigenvariables.  A builtin with a side effect,
such as `print`, inside the unwound part is not undone; while unwinding,
the alternatives of builtins with several solutions are still tried.)

**How skip works.**  `s` sets the stepping mode "skip #N", kept in a safe:
no event is shown or stops until the exit or fail port of call N
(breakpoints still stop).  Nothing in the run is undone or changed, the
local program and the scope included: the call runs as without the
debugger, unseen.  `o` (out) is a skip of the call whose body runs the event.

**For a front end** (`-machine`, [`lib/machine.elpi`](lib/machine.elpi)): besides the
usual text, elpi-debug prints lines `@@elpi-debug {JSON}`: first the
listing of the rules (numbered, with file and line) and of the lines of
the declarations; then, at each stop and in place of the prompt, the
description of the stop (its number, why it stops: `start`, `step`,
`breakpoint`, `pause`; the event; the stack of calls, each with the clause
it runs, its arguments and what each of its logic variables may depend on;
the bindings of a unify step; the local program; the eigenvariables).  The
run waits at a stop `Start` before its first event, where breakpoints can
be set.  The signal SIGUSR1 asks for a pause: the run stops at the next
event.  Only with `-machine`, the body of each clause runs under a local
clause `runs Id Origin` (the clause call #Id runs), which `=>` keeps
transparent to the cut; without it nothing changes.

Build and test: `cd elpi-tools && dune build && dune test`.  The tests
([`tests/*.t`](tests), dune cram tests) record traces, explanations,
breakpoints and stepping on five small programs (lists, cut, a typed
λ-calculus, CHR, a predicate defined nowhere) and check with `-compare`
that the interpreter gives the answers of the real engine;
[`tests/machine.t`](tests/machine.t) records a session of `-machine`.

## How the interpreter works

The interpreter is [`lib/`](lib), one file per concern; dune concatenates
them into `debug.elpi`, inside one `namespace debug { }` block (Elpi
resolves names block by block).  Read them in this order:

1. **[`state.elpi`](lib/state.elpi): the data.**  The options of `run`;
   the strategy, one value `strategy Order Solutions Depth Cut` (Elpi's
   own is `strategy in-order all-solutions unbounded honour-cut`); a
   `frame` per call (`#Id`, depth, predicate, goal), a `box` (a frame,
   the frames above it, how it was entered), a context `ctx` (where a goal
   runs); the safes that keep what must survive backtracking.
2. **[`program.elpi`](lib/program.elpi): the program as data.**  The
   driver ([`bin/`](bin)) runs elpi-reflect on FILE and compiles, in this
   order: `reflect.elpi`; `debug.elpi`; FILE **without its rules** (its
   declarations, so that the terms of the program type check, and its CHR
   rules, which run natively); the rules, as facts
   `reflect.clause P Index Loc Attrs Head Body`; and one **bridge** per
   predicate, `P X1..Xn :- !, debug.bridge (P X1..Xn)`, its only native
   rule, written by `write-bridges`.  They are static rules, not local
   clauses `pi x1..xn\ ...`: with those, Elpi crashes when a CHR rule fires
   ([LPCIC/elpi#505](https://github.com/LPCIC/elpi/issues/505)).
   `program-rule` gives the rules of a predicate, `modes-of` its modes.
3. **[`strategy.elpi`](lib/strategy.elpi): how a call is solved.**
   `candidate` gives the candidate clauses in Elpi's order (the hypothetical
   clauses in scope, most recent first, then the rules); `ordered-candidate`
   in the order of the strategy (or shuffled); `within-depth`,
   `keeps-first-solution`, `cut-ignored-here` read the rest of it.  With
   `random-order`, `first-solution`, `max-depth N`, `ignore-cut`, it is the
   random derivation of [`../check`](../check/README.md), which solves its
   `generated-by` premises with `debug.run` (its own solver,
   `check/lib/solve.elpi`, is gone; its reports are unchanged).
4. **[`interpreter.elpi`](lib/interpreter.elpi): the meta-interpreter.**
   - `run` installs the options, the strategy, the safes and the
     declarations as local clauses, and runs the query.
   - `compile` turns a clause body into a native goal, one clause per
     construct: a conjunction is compiled goal by goal; `pi`, `sigma`,
     `=>`, `;` stay native (with their ports); each atomic goal becomes
     `debug.goal Ctx G`.  **The cut** (the classic difficulty: a cut must
     discard the other clauses of the goal and the choice points before
     it, which belong to the interpreter, and Elpi has no "cut to here")
     stays a native cut: the compiled body runs as the last goal of
     `backchain`, so the cut discards exactly the remaining candidates of
     `backchain` and the choice points before it in the body, which is
     Elpi's semantics.  Elpi's cut goes through `pi`, `sigma`, `=>` and is
     local to `;` (checked on elpi 4.0.0); native connectives keep that.
   - `goal` dispatches a goal: a call of the program (`call`) or a builtin
     (`native`).
   - `call` builds the box and runs `attempt`, whose second clause is the
     choice point a retry or fail unwinds to; `box-ports` is Byrd's box
     (call, exit, redo, fail; the redo port is a clause tried when
     backtracking comes back into a call that exited).
   - `backchain` tries the candidates: head matching by the modes
     (`arg-match`: an input argument is matched with `pattern_match`, an
     output one unified), then the compiled body.
   - `assume` gives `H => G` its hypothetical clauses as data, facts
     `hyp P Origin C` added by the real `=>`: they have Elpi's scope and
     order, share their variables, get fresh ones for their `pi`.
5. **[`natives.elpi`](lib/natives.elpi): builtins, CHR, the way back.**
   `native` runs a builtin natively, with its ports; `delay` is the real
   `declare_constraint` (**CHR at depth 1**: the rules see the same
   constraints and fire natively), numbered; `bridge` brings a program
   goal called by native code (`not`, `std.map`, a woken constraint) back
   into the interpreter, where a woken goal enters through its resume port.
   (The design said `declare_constraint (solve G)`: changed, because the
   CHR rules would then not match the constraint.)
6. **[`lprolog.elpi`](lib/lprolog.elpi): λProlog in view.**  `shape-of`
   takes any term apart (Elpi has no builtin for λ-terms and connectives),
   for every walk: binders, logic variables, the clash of the explanation.
   `show-term` prints a term with the names of its eigenvariables (`x#3`,
   from the `eigen` clause in force in the scope of each `pi`);
   `can-depend` and `show-scope` tell which eigenvariables a logic variable
   may depend on.
7. **[`ports.elpi`](lib/ports.elpi): the events.**  `event` shows an event
   and stops there if needed; `port` for the ports of calls,
   `match-with-port` for the unify step (with the bindings and the pruning
   it made), `pi-port`, `assume-port`, `delay-port`, `cut-port`,
   `native-port`.
8. **[`stepper.elpi`](lib/stepper.elpi): interactive stepping.**  The
   stepping modes, the requests of retry and fail, the breakpoints, the
   command loop (how retry and skip work: above, and in the file).
9. **[`machine.elpi`](lib/machine.elpi): the machine-readable channel** of
   `-machine` (above, "For a front end"), with a small JSON writer.
10. **[`explain.elpi`](lib/explain.elpi): the explanation of a failure.**
   At the fail port of a call that never exited, where the goal is back as
   it was called: each candidate retried, the first argument that does not
   match and the smallest clashing subterms (`subterm-clash`), the occurs
   check and the scope of eigenvariables (`flex-clash`).
11. **[`profile.elpi`](lib/profile.elpi): the outcome and the profile.**

## Cost

Measured on 2026-11-18 on the laptop shared with other jobs (load about 5),
programs of [`tests/bench.elpi`](tests/bench.elpi), no option (with
`-trace` or `-profile` add the printing or the recording):

| goal | native | interpreted | ratio |
|---|---|---|---|
| `count 6400` (a countdown) | 0.007-0.009 s | 0.50-0.80 s | about 70-90 |
| `bench 200` (naive reverse, 20 000 calls) | 0.014 s | 1.2-2.2 s | about 90-150 |
| `queens 8 Q` | 0.007 s | 0.36-0.51 s | about 50-70 |

`-profile` multiplies these times by 2 to 5 (an event per port);
`-trace` costs the printing of each goal (36 s for `bench 200`, whose goals
hold lists of 200 elements).  Memory: 100 MB at most for `bench 200`.

So 50 to 150 times slower than the real engine, not the 10 hoped for in
the design: each call does the work of several dozen native ones (a box, a
safe for the explanation, the compilation of the body, mode-aware head
matching).  The cost per call is constant (it was first exponential, then
linear, in the depth of the recursion: Elpi copies or walks terms that hold
the stack of calls, through local clauses, the occurs check and input
arguments; the stack is now a flat list and the predicates that build terms
holding it are `:nooc`).

## Limits (said plainly)

- **Cut through a variable**: `G = !, ..., G` cuts only `G` itself (in Elpi
  it cuts the clause); a cut inside `not`, `std.findall`... is native, as in
  Elpi.
- **Conjunctions** of more than 16 goals at the same level are not taken
  apart (Elpi represents them as one node with no builtin to inspect it;
  there is one pattern per length).
- **Head patterns** `uvar` and `as` are supported only at the top of an
  argument.  `=!=>` and clause bodies given as lists (`H :- [B1, B2]`) are
  not supported.
- **CHR at depth 1 only**: the rules fire natively; the store and the
  rule attempts are not shown (only the delay and wake-up of interpreted
  goals; a refused constraint is explained as such).
- **Explanations** name the deepest failure, which is not always the
  culprit; failures inside `not` count as failures.
- Logic variables print as Elpi prints them (`X12`; Elpi's printer may give
  one variable different names in two lines), not with their source names.
  Eigenvariables get their source name (`x#3`) only when events are shown
  (`-trace`, `-i`, `-break`): on the fast path (no option) the explanation
  of a failure shows them as `c0`, `c1`.  The binder names come from
  reflect's `binders` attribute, matched with the binders of the rule in
  textual order; for a hypothetical clause or the query the name is `x`.
- An Elpi 4.0.0 crash met on the way: a CHR rule firing on a constraint
  whose predicate has a `pi`-quantified local clause in scope fails with
  `Invalid_argument("index out of bounds")`, reported upstream as
  [LPCIC/elpi#505](https://github.com/LPCIC/elpi/issues/505) (also on Elpi
  master 631d14a; minimal form in
  [`tests/elpi-bugs/chr-pi-local-clause.elpi`](tests/elpi-bugs/chr-pi-local-clause.elpi));
  it is why the bridges are static rules.
- **The driver uses `Obj.magic` once** (`to_api` in
  [`bin/elpi_debug_main.ml`](bin/elpi_debug_main.ml)), the one place
  where it goes around Elpi's API.
  - *Why*: the debugger must compile FILE **without its rules** (they are
    given to the interpreter as data; Elpi must not run them), together
    with the interpreter, the rules as facts and the bridges.  So it parses
    FILE, removes the rules, and compiles the result with other units.
    Elpi's API can parse and compile a file, but its parsed program
    (`API.Ast.program`) is abstract: it cannot be edited, nor joined with
    other units.  The driver therefore parses with the parser library
    (`Elpi_parser`), whose type it sees, and passes the edited program to
    `API.Compile.program` through `Obj.magic`.
  - *Why it works*: in elpi 4.0.0 the two types are one (`type program =
    Ast.Program.t` in `API.ml`), so the conversion is the identity.
  - *The risk*: nothing checks it.  If a later Elpi changes that type, the
    driver still compiles and then crashes or misbehaves at run time.  To
    be checked again with each new version of Elpi.
  - *The fix needs Elpi's API* (asked of its author): a function from the
    parser's program to the API's (`API.Ast.program_of_parsed`, say), or a
    way to compile a file without its rules, or to compile a program made
    of several parsed units.  The minimal example of the request:

    ```ocaml
    (* parse, drop the rules, compile: the last step has no API *)
    module PAst = Elpi_parser.Ast
    let without_rules (p : PAst.Program.t) =
      { p with ast = List.filter (function PAst.Program.Clause _ -> false | _ -> true) p.ast }
    let () =
      let elpi = API.Setup.init ~builtins:[ Builtin.std_builtins ] () in
      let module P = Elpi_parser.Parse.Make (struct
        let versions = Elpi_util.Util.StrMap.empty
        let resolver = API.Parse.std_resolver ~paths:[] ()
      end) in
      let parsed, _, _ = P.program_from ~loc:(Elpi_util.Util.Loc.initial "(source)")
          ~digest:(Digest.string source) (Lexing.from_string source) in
      let program : API.Ast.program = Obj.magic (without_rules parsed) in  (* no API for this *)
      ignore (API.Compile.program ~elpi program)
    ```

  - *Without an API change*, the other way is to give the declarations and
    the rules in two files (the user writes FILE's declarations apart), so
    that the driver compiles the file of declarations as it is: no cast,
    but a constraint on how programs are written.
