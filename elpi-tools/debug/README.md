# elpi-debug: a debugger for standalone Elpi

A debugger for Elpi 4 programs (standalone Elpi, opam switch `elpi5`; not
Rocq-Elpi), written as a **meta-interpreter in Elpi**
([`debug.elpi`](debug.elpi)).  It runs a goal by interpreting the rules of
the program, which [`../reflect`](../reflect/README.md) gives as Elpi data,
and shows what the real engine does not:

- the four **ports** of each call (call, exit, redo, fail, as in Prolog
  tracers), plus the cut, the suspension of a goal by `declare_constraint`
  and its **wake-up** by CHR;
- **breakpoints** on a predicate, with the calls above, the hypothetical
  clauses in scope (and the call that added each one) and the
  eigenvariables; interactive stepping;
- **counts and time per predicate** (calls, exits, redos, fails, clauses
  tried, self time);
- on failure, an **explanation**: the deepest goal that failed at its first
  try, the calls above it, every clause tried and why it did not apply (the
  argument and the smallest subterms that clash, an input argument that the
  goal leaves unknown, the occurs check), or that the predicate **has no
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
| `-i` | at a stop, read commands on stdin: `c` continue, `s` step (stop at every port), `t` trace, `b` backtrace, `h` hypotheses and eigenvariables, `e` deepest failure so far, `a` abort |
| `-profile` | ports and self time per predicate |
| `-no-explain` | no explanation of a failure |
| `-all`, `-n N` | all the solutions (at most N), not only the first |
| `-native` | run the goal with the real engine instead |
| `-compare` | run with both, compare all the answers (exit code 1 if they differ) |
| `-random SEED`, `-first`, `-max-depth N`, `-ignore-cut` | the strategy (below) |
| `-time`, `-warnings`, `-I DIR` | |

`ELPI_DEBUG_TRACE="-trace-on tty stdout ..."` passes options to Elpi's own
tracer (to debug the debugger).

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
- Variables print as Elpi prints them (`X12`, eigenvariables `c0`), not with
  their source names.
- An Elpi 4.0.0 crash met on the way: a CHR rule firing on a constraint
  whose predicate has a `pi`-quantified local clause in scope fails with
  `Invalid_argument("index out of bounds")`
  ([`tests/elpi-bugs/chr-pi-local-clause.elpi`](tests/elpi-bugs/chr-pi-local-clause.elpi));
  it is why the bridges are static rules.
- The driver hands the parsed program to the compiler with `Obj.magic`:
  Elpi's API has no function for a program built from parsed units, but its
  type of parsed programs is the parser's own (`type program =
  Ast.Program.t` in elpi 4.0.0's `API.ml`).
