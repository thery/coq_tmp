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
  by `declare_constraint` and its **resume** by CHR, numbered (`[S2]`); at
  the **exit** port, what the whole call computed (the bindings it made
  since its call port); a logic variable keeps one name, `X3`, for the
  whole run;
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
      X0 := 6
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

**What a call computed.**  When the call port of a call is shown or
stopped at, the debugger marks the trail there; its exit port then shows
the bindings made since, by its unify steps and by the calls of its body
(`Exit: #1 double 3 6` above, with `X0 := 6`: the variable of the goal at
the call port, bound by a call inside, after a CHR resume).  A call that
is not seen at its call port takes no mark (its exit, if shown, has no
bindings): with `-profile`, or between breakpoints, nothing of this runs.

**For a front end** (`-machine`, [`lib/machine.elpi`](lib/machine.elpi)): besides the
usual text, elpi-debug prints lines `@@elpi-debug {JSON}`: first the
listing of the rules (numbered, with file and line) and of the lines of
the declarations; then, at each stop and in place of the prompt, the
description of the stop (its number, why it stops: `start`, `step`,
`breakpoint`, `pause`; the event; the stack of calls, each with the clause
it runs, its arguments and what each of its logic variables may depend on;
the bindings of a unify step or of an exit port; the local program;
the eigenvariables; the variables of the query by their source names,
`L` of `append [1] [2] L`, with their values, which the driver finds in
the goal and passes to `debug.run` as the option `debug.query-vars`).  The
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
   `reflect.clause P Index Loc Attrs Head Body` and, closed, as facts
   `reflect.closed-clause N F` (elpi-reflect `-closed`: F is the rule under
   N binders, one per variable: the debugger cannot close a rule itself,
   its walk does not see the variables inside applications of builtins;
   "The primitives" below); and one **bridge** per
   predicate, `P X1..Xn :- !, debug.bridge (P X1..Xn)`, its only native
   rule, written by `write-bridges`.  They are static rules, not local
   clauses `pi x1..xn\ ...`: with those, Elpi crashes when a CHR rule fires
   ([LPCIC/elpi#505](https://github.com/LPCIC/elpi/issues/505)).
   `program-rule` gives the rules of a predicate, `modes-of` its modes.
3. **[`strategy.elpi`](lib/strategy.elpi): how a call is solved.**
   `candidate` gives the candidate clauses in Elpi's order as data (the
   hypothetical clauses in scope, most recent first, then the rules), for
   the explanation.  The predicates of a call that depend on the strategy,
   `solutions`, `within-depth` and `ordered-clause` (the compiled clauses
   in the order of the strategy), have no clause of their own: `run`
   installs those of its strategy (`strategy-clauses`), so that a call does
   not look the strategy up.  In a random order, with the cut ignored the
   candidates are tried one by one by reference; with the cut honoured the
   clauses of the call are installed again for it alone, shuffled, so that a
   cut discards those after it.  With
   `random-order`, `first-solution`, `max-depth N`, `ignore-cut`, it is the
   random derivation of [`../check`](../check/README.md), which solves its
   `generated-by` premises with `debug.run` (its own solver,
   `check/lib/solve.elpi`, is gone; its reports are unchanged).
4. **[`interpreter.elpi`](lib/interpreter.elpi): the meta-interpreter.**
   - `run` installs the options, the strategy, the safes, the
     declarations and the compiled rules (compiled.elpi) as local clauses,
     and runs the query.
   - `compile` turns a clause body into a native goal, one clause per
     construct: a conjunction is compiled goal by goal; `pi`, `sigma`,
     `=>`, `;` stay native (with their ports); an atomic goal of a declared
     predicate becomes `debug.call`, of another constant
     `debug.undeclared-goal` (a builtin, or hypothetical clauses only), and
     any other `debug.goal`, dispatched when it runs.  The code has no
     variable of its own (sigma binds those it needs), so a clause is
     compiled once.  **The cut** (the classic difficulty: a cut must
     discard the other clauses of the goal and the choice points before
     it, which belong to the interpreter, and Elpi has no "cut to here")
     stays a native cut: the compiled body is the body of a local clause of
     `compiled`, so the cut discards exactly the other candidates of the
     goal and the choice points before it in the body, which is Elpi's
     semantics.  Elpi's cut goes through `pi`, `sigma`, `=>` and is
     local to `;` (checked on elpi 4.0.0); native connectives keep that.
   - `goal` dispatches a goal: a call of the program (`call`) or a builtin
     (`native`).
   - `call` builds the box and runs `run-box`: on the fast path (no event
     shown or recorded, so no stop and no retry) only its solutions and the
     note of its failure; otherwise `attempt`, whose second clause is the
     choice point a retry or fail unwinds to; `box-ports` is Byrd's box
     (call, exit, redo, fail; the redo port is a clause tried when
     backtracking comes back into a call that exited).
   - `backchain` calls the compiled clauses of the goal (`ordered-clause`).
   - `assume` gives `H => G` its hypothetical clauses as data, facts
     `hyp P Origin C` added by the real `=>`, and compiled: they have
     Elpi's scope and order, share their variables, get fresh ones for
     their `pi`.
   - **[`compiled.elpi`](lib/compiled.elpi): the clauses compiled once.**
     Each rule (from its closed form, instantiated with eigenvariables that
     become the binders of the result) and each hypothetical clause becomes
     a local clause `compiled G Key Id Ctx :- Rest, Body`: its head is the
     head of the rule up to its first argument that needs more than
     matching (an output, a `uvar` or `as` pattern), so Elpi itself selects
     the candidates, with its indexing (`:index(2)`: the first-argument
     indexing of Elpi and more), and matches them; `Rest` does the other
     arguments in order (`match-arg`, `unify-arg`: head unifications, which
     do not walk the goal as `=` and `pattern_match` do), with the unify
     event; `Body` is the compiled body.  It returns nothing: Elpi makes the
     occurs check on every local clause (`:nooc` does not apply to them), so
     an output would walk the stack of calls.  `with-rule-cache G` keeps the
     compiled rules across the runs of G (elpi-check uses it).
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
   for every walk: binders, the stand-in of `vars-of`, the clash of the
   explanation.  `show-term` prints a term with its logic variables named
   `X<uuid>` and its eigenvariables by their source names (`x#3`, from the
   `eigen` clause in force in the scope of each `pi`); `can-depend` and
   `show-scope` tell which eigenvariables a logic variable may depend on.
7. **[`primitives.elpi`](lib/primitives.elpi): the variables of a run**,
   through three primitives (four predicates) that Elpi's core could
   offer, written in Elpi as stand-ins for now (below, "The
   primitives"): `vars-of`, `uuid`, `trail-mark` and `bindings-since`.  The other files know the variables
   of a run only through them.
8. **[`ports.elpi`](lib/ports.elpi): the events.**  `event` shows an event
   and stops there if needed; its text is made only then (a closure:
   `port-text`, `unify-text` ...); `port` for the ports of calls
   (`call-port-marked` marks the trail at a call port seen, and
   `exit-port-with-bindings` shows what the call computed),
   `unify-port` for the unify step (a mark of the trail before the end of
   the head unification, the bindings since after it, the pruning
   included), `pi-port`, `assume-port`, `delay-port`, `cut-port`,
   `native-port`.
9. **[`stepper.elpi`](lib/stepper.elpi): interactive stepping.**  The
   stepping modes, the requests of retry and fail, the breakpoints, the
   command loop (how retry and skip work: above, and in the file).
10. **[`machine.elpi`](lib/machine.elpi): the machine-readable channel** of
   `-machine` (above, "For a front end"), with a small JSON writer.
11. **[`explain.elpi`](lib/explain.elpi): the explanation of a failure.**
   At the fail port of a call that never exited, where the goal is back as
   it was called: each candidate retried, the first argument that does not
   match and the smallest clashing subterms (`subterm-clash`), the occurs
   check and the scope of eigenvariables (`flex-clash`).
12. **[`profile.elpi`](lib/profile.elpi): the outcome and the profile.**

## The primitives (what Elpi's core could offer)

Everything the debugger knows about the logic variables of a run goes
through three primitives (four predicates) of
[`lib/primitives.elpi`](lib/primitives.elpi), a small interface that
Elpi's core could provide as builtins (the wish list, for Elpi's author: [`ELPI-WISHLIST.md`](ELPI-WISHLIST.md)).  Until
then they are written in Elpi, as **stand-ins**; the switch to real
builtins would touch that file only.

| primitive | contract | used by |
|---|---|---|
| `vars-of T Vs` | the logic variables of T, each once, in order, under binders and inside applications of builtins; binds nothing | the trail mark (the variables in reach), `scope`, the scopes of `-machine`, the occurs check of the explanation |
| `uuid X N` | a number for the variable X, the same at every event and across backtracking; elpi-debug shows X as `X<N>` everywhere (traces, explanations, `-machine`) | every name of a variable (`show-term`, `uuid-name`) |
| `trail-mark M`, `bindings-since M Bs` | the bindings made since the mark M and still in force, keyed by uuid, the pruning reported (a variable replaced by one with fewer arguments, or a smaller scope of eigenvariables) | the unify step (mark, the end of the head unification, bindings since); the exit port (mark at the call port, bindings at the exit) |

Before, these were three workarounds spread over the files: a walk for the
variables of a term (`logic-vars`), a variable known only by how Elpi
prints it, and the bindings of a unification found by printing every
variable of the goal before and after and comparing the strings (the
pruning by comparing scopes).

**The stand-ins, and their limits** (in the file, at the top):

- `vars-of` is the walk of `shape-of`.  It cannot look inside an
  application of a builtin (`X is Y + 1` is one node for Elpi), nor into a
  conjunction of more than 16 goals.  The head of an applied variable is
  got with the builtin `var`; on a variable that Elpi keeps in a compact
  form (`G x`, x the binder just above, printed `X0^1` by Elpi) that head
  is a new variable, bound in place of the old one, so the variable then
  shows under a second number (`same X0 (X1 x#1 x#2)` at the call port,
  `X2 := ...` at the unify step, in `tests/interactive.t`).
- `uuid` reads the number of the variable in Elpi's printer: the printer
  keeps for the whole run a table from Elpi's internal identity of a
  variable to the number it gives at its first print, the one place where
  a program sees that identity.  A table of the debugger's own cannot do
  it: a safe refuses a term with variables, a local clause does not
  outlive the goal that adds it, and `same_var` cannot tell a variable
  from one bound to it.  Inside `std.findall` the stand-in is wrong (the
  goal is copied, and printed with a table of its own from `X0`): the
  debugger no longer prints variables inside `std.findall` (the local
  program of `-machine` was printed there, with wrong names: fixed).
  The depth suffix of Elpi's names (`X3^1`) is dropped: `X3` is the name.
- `trail-mark` cannot see Elpi's trail: it is a snapshot of the variables
  in reach, which the caller gives (`trail-mark Reach M`, Reach a closure
  that the real builtin would not call), and `bindings-since` compares
  them with what they are now.  In reach of a goal: its variables and
  those of the hypothetical clauses in scope (a clause added by `=>`
  shares its variables with the goal that added it; the frames above give
  no other access to a variable).  Missed: a variable reached only through
  a goal suspended in the constraint store, or inside an application of a
  builtin.  Cost: a walk of the goal and the hypotheses at the mark, and a
  test per variable at `bindings-since`; only for an event shown or
  stopped at.

Nothing of this runs on the fast path (no option), and a call port that
is neither shown nor stopped at takes no mark.

**What the real builtins would bring.**

- `vars-of` in OCaml: the variables inside applications of builtins, no
  binding when it looks (the names would not drift as above), and a walk
  at the speed of the runtime instead of several interpreted goals per
  node (`shape-of` tries its clauses in turn).
  With it the debugger could close the rules of the program itself (fetch
  a rule under `pi x1..xn\`, bind its n variables to the x's), and the
  detour through elpi-reflect's option `-closed` (each rule printed a
  second time, closed, as `reflect.closed-clause N F`) would go.
- `uuid`: the identity without printing (the stand-in prints each
  variable it names); right inside copies too.  The printer itself could
  name variables by it: Elpi's printer has the line, commented out
  (`"X" ^ string_of_int (uvar_id r)`, runtime.ml), so `show-term` would
  be one builtin call.
- `trail-mark` and `bindings-since` on the real trail: exact (every
  variable bound since the mark, whatever reaches it: the constraint
  store, builtins), and a cost proportional to the bindings made, not to
  the size of the goal and of the hypotheses: the mark would cost nothing,
  so every call could take one (today only the calls seen at their call
  port do).

**Could retry use the trail?**  Today `r` unwinds by failing: a pending
request makes every event fail, so backtracking goes through every choice
point inside the call until the second clause of `attempt` (above, "How
retry and fail work").  Undoing the bindings to the mark of the call port
is not enough: the choice points created since would still be there, and
backtracking into them would redo the work with bindings in an
inconsistent state.  What retry needs is a "backtrack to this point"
primitive: a mark that also records the choice-point stack, and a builtin
that drops the choice points created since and undoes the trail to the
mark in one step (a cut-and-fail to a given choice point, as Prolog's
catch/throw does).  With it, retry would be immediate and would not run
the builtins with several solutions met while unwinding.  This is not in
the wish list's first three items: it touches the core of Elpi's machine,
not only its data.

## Cost

Measured on 2026-11-19 on the laptop shared with other jobs (load about
3), programs of [`tests/bench.elpi`](tests/bench.elpi), no option, the
minimum of 10 runs alternated with the version before this work (main of
2026-11-18):

| goal | native | interpreted | ratio | before |
|---|---|---|---|---|
| `count 6400` (a countdown) | 0.007 s | 0.15 s | about 22 | 0.61 s, 88 |
| `bench 200` (naive reverse, 20 000 calls) | 0.014 s | 0.30 s | about 22 | 1.32 s, 94 |
| `queens 8 Q` | 0.005 s | 0.10 s | about 21 | 0.33 s, 65 |
| `lookups 2000` (a predicate of 200 facts) | 0.006 s | 0.11 s | about 19 | 3.0 s, 500 |

At load 5.5 the same runs gave 0.13, 0.28 and 0.09 s (19, 22, 13-18): the
ratios move by about 20 % with the load of the machine.

**Where the time went** (measured before the changes, on these
benchmarks): by switching off one mechanism at a time, by micro-benchmarks
of each step of a call in the context of `run`, and by counting the goals
Elpi runs per call (`ELPI_DEBUG_TRACE`, `-trace-only user:curgoal`).  One
goal of the interpreter costs about 0.5 µs; a native call about 0.5 µs.

- **Binding a variable to a large term walks it.**  Elpi's `=`,
  `pattern_match` and the outputs of builtins (`constant G P Args`) make
  the occurs check: 20 µs to bind a variable to a list of 200 elements
  (0.1 µs per element).  Head matching argument by argument did it at
  each call on every argument of the goal: replacing it by a plain `G =
  Head` took `bench 200` from 1.45 to 0.92 s.  Head unification of a
  `:nooc` static clause does not walk; that of a **local** clause always
  does (Elpi makes the occurs check on every hypothetical clause), which
  ruled out local clauses that return terms holding the goal or the stack.
- **The compilation of the body at each call**, and the dispatch of each
  of its goals (a builtin or a call): 16 µs for the body of `count`; the
  two together, with the wrapper of builtins, about half of `count` and
  two thirds of `queens`.
- **A walk of each builtin goal** to decide whether it may call back the
  program: 20-30 µs for `X is 3 - 1`, while installing the context it
  needs costs under 1 µs whatever its size: 20 % of `count`, 26 % of
  `queens`.
- **No indexing within a predicate**: every rule of the predicate tried,
  its head matched: `lookups 2000` 500 times slower than native.
- Smaller: the strategy and the options looked up at each call (9 of the
  26 goals of a call of `app` after the changes below), the ports and the
  choice point for a retry on the fast path (where no event is shown).

**The changes**, each measured on the three benchmarks (load 4-5):

| change | count 6400 | bench 200 | queens 8 |
|---|---|---|---|
| before | 0.63 s | 1.35-1.45 s | 0.31 s |
| a builtin always gets the context of its call backs (no walk) | 0.52 | 1.38 | 0.24 |
| the clauses compiled once into local clauses that Elpi selects and matches (`compiled.elpi`) | 0.19 | 0.39 | 0.13 |
| fast path: no ports, no retry point; builtins dispatched when compiling | 0.141 | 0.317 | 0.094 |
| the strategy and the fast path as clauses installed by `run` | 0.130 | 0.281 | 0.090 |

The first version of the compiled clauses returned the compiled body from
a local clause: quadratic (`count 6400` 4.5 s), because of the occurs
check of local clauses above; the clauses now do their work in their body.
elpi-check runs `debug.run` once per test case, and compiling the rules at
each run cost 4 ms on `stlc.elpi` (about 120 µs per rule): with
`debug.with-rule-cache` it compiles them once; its tests: `stlc` 9.3 s
before, 9.6 s now (within the noise), `rev`, `sort`, `strings` unchanged,
the same reports.

**With events.**  An event used to print its goal into its text even when
it was neither shown nor stopping (with `-profile`, with `-machine`
between stops, with `-break`); the text is now made only then.
Configuration 7 of [`../demo/.vscode/launch.json`](../demo/.vscode/launch.json)
(`std.iota 200 L, naive-rev L R1, rev L R2`, min of 3), before this work
-> before this change -> now: `-machine -profile` 12.5 -> 8.8 -> 4.9 s,
`-machine` 10.3 -> 6.4 -> 2.1 s, `-profile` 12.1 -> 8.1 -> 4.0 s,
`-break nowhere` 9.8 -> 5.4 -> 1.4 s; no option 1.6 -> 0.46 s.

**The primitives and the Exit bindings** (2026-11-19, load 2.3-4.4,
minimum of 10 runs alternated with main of the same day, interpreted time
of `-time`):

| run | before | after |
|---|---|---|
| `count 6400` | 0.155 s | 0.147 s |
| `bench 200` | 0.309 s | 0.296 s |
| `queens 8 Q` | 0.102 s | 0.098 s |
| `lookups 2000` | 0.116 s | 0.110 s |
| `-profile`, configuration 7 | 3.80 s | 3.85 s |
| `-machine`, configuration 7, no stop asked | 1.79 s | 1.85 s |
| `-trace bench 30` (465 calls on lists, output to /dev/null) | 0.42 s | 0.63 s |

The fast path is unchanged (within the noise).  `-profile` and
`-machine` without stops: about 2 % (an extra goal per event).  `-trace`
is about 50 % slower: each call port shown now takes a mark (a walk of the
goal and of the hypotheses in scope) and its exit prints the bindings
made since (about 0.15 s of the 0.21 s, measured by switching the mark
off); the rest is the stand-in of `uuid` (a print per variable named) in
the unify step.  The real builtins would remove most of it.

**What is left.**  A call still runs about 26 goals of the interpreter
(`app`), a builtin about 14 more than its own: a box with an invocation
number, a safe for the explanation (needed for the warning of a predicate
with no clause), the depth, the context.  With events on, each event
looks up the breakpoints and the stepping mode in their safes (about 137
goals per call with `-break`, against 26 on the fast path): not changed
here.  `-trace` still costs the printing of each goal.
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
- Logic variables are named `X<uuid>` (`X12`), one name per variable for
  the whole run, not with their source names (except the variables of the
  query, by their names in the stop description of `-machine`).  With the
  stand-in of `vars-of`, a variable kept by Elpi in a compact form gets a
  second number when the debugger first looks at it (above, "The
  primitives").  Eigenvariables get their source name (`x#3`) only when
  events are shown (`-trace`, `-i`, `-break`): on the fast path (no
  option) the explanation
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
