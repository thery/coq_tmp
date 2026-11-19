# check: properties of Elpi programs, tested at random

[← overview](../DESIGN.md) · README: [`../check/README.md`](../check/README.md)

## What

A program states properties next to its predicates; `elpi-check FILE`
tests each one on random values (100 by default, sizes growing from 1 to
20) and reports the smallest counterexample it finds.  From
[`../check/tests/sort.elpi`](../check/tests/sort.elpi):

```elpi
accumulate property.

func insert-wrong int, list int -> list int.
insert-wrong X [] [X].
insert-wrong X [X | L] [X | L] :- !.                 % the bug: X is lost
insert-wrong X [Y | L] [X, Y | L] :- X =< Y, !.
insert-wrong X [Y | L] [Y | R] :- insert-wrong X L R.

property "insert-length"
  (pi X L R N M\ insert-wrong X L R ==> std.length L N ==> std.length R M ==> M is N + 1).
property "insert-sorted"
  (pi X L R\ sorted L ==> insert X L R ==> sorted R).
```

```
$ elpi-check sort.elpi        # in check/tests/
property insert-sorted (sort.elpi:25)
  variables: X : int (generated), L : list int (generated), R : list int (computed)
  OK: passed 41 tests, 59 discarded; average size of the values 3
property insert-length (sort.elpi:29)
  variables: X : int (generated), L : list int (generated), R : list int (computed), N : int (computed), M : int (computed)
  FAILED at test 38 (37 passed, 0 discarded); first counterexample:
    X = 7
    L = [7, -1]
    R = [7, -1]
    N = 2
    M = 2
  shrunk in 2 steps to:
    X = 0
    L = [0]
    R = [0]
    N = 1
    M = 1
…
elpi-check: 2 of 4 properties hold (seed 1)
```

## How

### A property is a fact, and λProlog's own logic

```elpi
pred property o:string, o:(pred).          % check/lib/property.elpi
property "name" (pi X\ … Premise ==> … ==> Conclusion).
```

The program still runs as before (the facts are inert) and **Elpi type
checks the property with the program**.  elpi-check reads the formula as
data, does not run it as a goal (running `A ==> B` would *assume* A).

### Generated or computed: the modes decide

[`../check/lib/analyse.elpi`](../check/lib/analyse.elpi): reading the
premises left to right, a variable first met in an **output** argument is
computed by that premise; one first met in an **input**, or only in the
conclusion, is generated from its type.  In `insert-length`, `X` and `L`
are inputs of `insert-wrong` (`func insert-wrong int, list int -> …`):
generated; `R`, `N`, `M` are outputs: computed.  Types come from the
signatures and the constructors, as reflect gives them; an open type
parameter is `int`.

### Generation from the declared types

[`../check/lib/generate.elpi`](../check/lib/generate.elpi)`:term.of`: a
value is built from the constructors of its type with a budget S; leaves
first with probability 1/S; an argument of type `A -> B` is built under
`pi x\` with `x` as a leaf:

```elpi
term.of (reflect.tarrow A B) S F :- !, pi x\ bound-var x A => term B S (F x).
term.of T S X :-
  choices T Leaves Nodes,
  order S Leaves Nodes Ordered,
  first-built Ordered T S X.
```

So lists have a length uniform on 0..S-1 (measured), and closed λ-terms
such as `lam (c0 \ app c0 c)` come out directly.

### `generated-by`: values that satisfy a premise, by a random derivation

A premise `generated-by G` is solved at random: its variables come out of
a random derivation of G, so they satisfy G by construction — the idea of
Blanco, Miller and Momigliano.  The solver is **the debugger's
meta-interpreter with a random strategy**
([`../check/lib/run.elpi`](../check/lib/run.elpi)`:generators`):

```elpi
generators Size (generated-by G ==> B) :- !,
  debug.run [debug.random-order, debug.first-solution, debug.max-depth Size,
             debug.ignore-cut, debug.no-explain] G, !,
  generators Size B.
```

On the simply typed λ-calculus of [`../demo/lambda.elpi`](../demo/lambda.elpi),
with a wrong reduction rule (`step (app M _) M`):

```
$ elpi-check -I ../check/lib -p preservation lambda.elpi        # in demo/
property preservation (lambda.elpi:30)
  variables: M : tm (generated-by), T : ty (generated-by), N : tm (computed)
  FAILED at test 16 (0 passed, 15 discarded); first counterexample:
    M = app (app (app (lam (c0 \ c0)) (lam (c0 \ c0))) (lam (c0 \ app c0 c))) (lam (c0 \ c))
    T = base
    N = app (app (lam (c0 \ c0)) (lam (c0 \ c0))) (lam (c0 \ c))
  shrunk in 3 steps to:
    M = app (lam (c0 \ c)) c
    T = base
    N = lam (c0 \ c)
```

Every M tested is well typed: `of M T` was derived, not checked.

### Shrinking

[`../check/lib/shrink.elpi`](../check/lib/shrink.elpi)`:candidate`, greedy:
the leaves of the type, the subterms of the same type, one argument
shrunk; for an int 0, N/2, N-1.  Every candidate weighs strictly less
(size plus absolute values), so the loop stops.  Values from
`generated-by` are shrunk too, the premise then checked natively.  When
no single value shrinks, a literal occurring more than once is replaced
everywhere at once (`X = 7, L = [7]` shrinks to `X = 0, L = [0]`).

### The replay goal

The shrunk counterexample becomes a goal for the debugger: the premises
and the conclusion, the generated variables replaced by their values,
the computed ones left as variables; if that goal has a solution
natively (the premises have several), the computed values are pinned
after the premises ([`../check/lib/replay.elpi`](../check/lib/replay.elpi)).
For `preservation`:

```
$ elpi-check -json -I ../check/lib -p preservation lambda.elpi | grep -o '"replay":[^}]*'
"replay": "of (app (lam (c0 \\ c)) c) base, step (app (lam (c0 \\ c)) c) N, N = lam (c0 \\ c), of N base"
$ elpi-debug -I ../check/lib lambda.elpi 'of (app (lam (c0 \ c)) c) base, step (app (lam (c0 \ c)) c) N, N = lam (c0 \ c), of N base'
debug: no (more) solution.
Deepest failure (depth 2): #7 step c (X9 c0)
  called from:
    #6 step (lam c1 \ c) (lam X9)
    #5 step (app (lam c1 \ c) c) (app (lam X9) c)
  clauses tried:
    lambda.elpi:24: step (app (lam X0) X1) (X0 X1)
        does not match: argument 1 (input): c vs app (lam X0) X1
…
No solution.
```

(The explanation names the deepest failure, here in the backtracking of
the premise `step`, not the conclusion: stepping shows the conclusion
`of N base` failing; dap README, Manual check, step 5.)  In VS Code, "Debug
this counterexample" starts the debugger on this goal (design/dap.md).

## Why this way

- **Properties in the program, type checked by Elpi**, rather than a
  separate test file or strings: a property about `insert X L R` with the
  wrong arity is a compile error.  The formula is λProlog's (`pi`, `==>`),
  so its reading is the logical one.
- **Modes, not annotations, decide what is generated.**  Generating an
  output at random (`R` in `insert X L R`) would make the premise false
  almost always; Elpi 4 declares modes anyway.
- **One random solver: the debugger's interpreter.**  elpi-check first
  had a solver of its own (stlc 2.9-3.8 s); it now calls `debug.run` with
  a random strategy (8.5-13 s, 2-3 times slower, same reports, measured
  2026-11-18 on a loaded laptop).  The gain: one meta-interpreter, the
  same treatment of `pi`, `=>` and hypothetical clauses, and the rules
  compiled once per run (`debug.with-rule-cache`).  Not Elpi itself with
  shuffled clauses: Elpi has no way to choose the order of the clauses of
  a call at random, nor a depth bound.
- **Reproducible**: each property draws from a random stream of its own,
  started from the seed and its name, so `-p NAME` gives the same
  counterexample as the whole file.
- **Limits** (README): no time bound per test; the random solver ignores
  cuts and keeps the first solution of each call; at most 10 conjuncts
  where the checker looks into a conjunction (one pattern per length:
  requested feature 9).
