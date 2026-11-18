# elpi-debug: a debugger for standalone Elpi

A debugger for Elpi 4 programs (standalone Elpi, opam switch `elpi5`; not
Rocq-Elpi), written as a **meta-interpreter in Elpi**
([`debug.elpi`](debug.elpi)).  It runs a goal by interpreting the rules of
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
  Call: #2 even X0
  Cut:  #2 commits to its current clause
    (builtin) delay: even X0
  Exit: #2 even X0
    Wake: #3 even 6
    Exit: #3 even 6
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
| `l` | leap: run to the next breakpoint |
| `t` | trace: show every event, stop only at breakpoints |
| `n` | nodebug: run to the end (also at the end of stdin) |
| `r` | retry this call from its call port |
| `f` | make this call fail |
| `p` | print the goal, the local program and the scope |
| `g` | the calls above |
| `scope` | the eigenvariables in force and, for each logic variable of the goal, those it may depend on |
| `hyps` | the local program (the clauses added by `=>`, with the call that added each) |
| `+ P`, `- P` | set, remove a breakpoint on the predicate P |
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
call port (or shows its fail port and fails).  The **local program and the
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
debugger, unseen.

Build and test: `cd elpi-tools && dune build && dune test`.  The tests
([`tests/*.t`](tests), dune cram tests) record traces, explanations,
breakpoints and stepping on five small programs (lists, cut, a typed
λ-calculus, CHR, a predicate defined nowhere) and check with `-compare`
that the interpreter gives the answers of the real engine.

## How it works

**The program as data.**  The driver ([`bin/`](bin), OCaml on the `elpi`
library) runs elpi-reflect on FILE and compiles, in this order:
`reflect.elpi`; `debug.elpi`; FILE **without its rules** (its
declarations, so that the terms of the program type check, and its CHR
rules, which run natively); the rules as facts
`reflect.clause P Index Loc Attrs Head Body`; and one **bridge** per
predicate, `P X1..Xn :- !, debug.bridge (P X1..Xn)`, its only native rule.
The bridges are static rules, written by `debug.write-bridges`, and not
local clauses `pi x1..xn\ ...` installed by the interpreter: with those,
Elpi crashes when a CHR rule fires
([LPCIC/elpi#505](https://github.com/LPCIC/elpi/issues/505)).
The query is `debug.run Options (GOAL)`.

**Goals.**  Conjunction, `pi`, `sigma`, `=>`, `;` and the cut keep Elpi's
own meaning; a goal of a program predicate gets a box with its ports and is
solved by backchaining on its candidate clauses: the hypothetical clauses
in scope (most recent first), then the rules of the program in Elpi's order.
Head matching follows the declared modes: an input argument is matched
(`pattern_match`, the goal's variables are not assigned), an output one is
unified.  Builtins run natively.  Native code that calls a program
predicate back (`not`, `std.map`, `std.findall`, a woken constraint) reaches
the interpreter through the bridge, so these calls have their ports too.

**Hypothetical clauses as data.**  `H => G` adds `debug.hyp P Origin C` for
each clause C of H, with the real `=>`: the hypotheses get Elpi's scope and
order, keep their variables shared and their `pi`-bound variables fresh.

**The cut** (the classic difficulty of a meta-interpreter: Elpi has no "cut
to here").  A clause body is not interpreted goal by goal: it is
*compiled* into a native goal in which each atomic goal G becomes
`debug.goal Ctx G` and the connectives and the cut stay native.  The
compiled body is the last goal of the interpreter's clause that selects
the candidate clauses, so a native cut there discards exactly the other
candidates and the choice points of the goals before it: Elpi's semantics.
Since Elpi's cut goes through `pi`, `sigma` and `=>` and is local to `;`
(checked on elpi 4.0.0), keeping these connectives native keeps that too.

**CHR at depth 1.**  `declare_constraint G Keys` is the real one, so the
CHR rules see the same constraints and fire natively; when G is woken, its
bridge brings it back into the interpreter, through a `Wake` port (the
RESUME port of ECLiPSe).  The design said `declare_constraint (solve G)`:
changed, because the CHR rules would then not match the constraint.

**Ports and state.**  Byrd's box: the redo port is a clause tried when
backtracking reaches a box that has exited.  What must survive
backtracking (the deepest failure, the stepping mode, the profile events)
is kept in Elpi safes.  The explanation is computed at the fail port, where
the goal is back as it was called, by retrying every candidate's head; only
goals that fail at their first try count (a fail after a redo is the normal
end of an enumeration).

**The strategy.**  By default Elpi's: candidates in order, with
backtracking.  Options change it: `random-order` (with `seed N`),
`first-solution` (each call keeps its first solution), `max-depth N`,
`ignore-cut`.  With all four it is the random derivation used by
[`../check`](../check/README.md) to solve `generated-by` premises, which
now calls `debug.run` (it had its own solver, `check/lib/solve.elpi`,
removed; the checker's reports are unchanged).

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
- The driver hands the parsed program to the compiler with `Obj.magic`:
  Elpi's API has no function for a program built from parsed units, but its
  type of parsed programs is the parser's own (`type program =
  Ast.Program.t` in elpi 4.0.0's `API.ml`).
