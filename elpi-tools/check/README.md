# elpi-check: properties of Elpi programs, checked by random testing

A program states properties next to its predicates; `elpi-check` tests
them on random values, QuickCheck style, and reports the smallest
counterexample it finds.  Standalone Elpi 4 (opam switch `elpi5`), not
Rocq-Elpi.

```elpi
accumulate property.

func rev list A -> list A.
rev L R :- rev.aux L [] R.
...
property "rev-involutive" (pi L R L2\ rev L R ==> rev R L2 ==> L2 = L).
property "rev-identity"   (pi L R\ rev L R ==> R = L).          % false
```

```
$ elpi-check rev.elpi
property rev-involutive (rev.elpi:15)
  variables: L : list int (generated), R : list int (computed), L2 : list int (computed)
  OK: passed 100 tests, 0 discarded; average size of the values 11
...
property rev-identity (rev.elpi:20)
  variables: L : list int (generated), R : list int (computed)
  FAILED at test 14 (13 passed, 0 discarded); first counterexample:
    L = [0, -1]
    R = [-1, 0]
  shrunk in 0 steps to:
    L = [0, -1]
    R = [-1, 0]
elpi-check: 2 of 3 properties hold
```

    elpi-check [-n TESTS] [-size SIZE] [-seed SEED] [-p PROPERTY] [-I DIR].. [-D VAR].. [-v] FILE

`-n` tests per property (100), `-size` largest size (20), `-seed` (1: the
runs are reproducible), `-p` one property only, `-v` the compiler's
warnings.  The exit code is 0 when every property holds, 1 otherwise, 2 for
an error in the program.

## The syntax of properties, and why

```elpi
property "name" Formula.

Formula ::= pi X\ Formula          % a variable of the property
          | Premise ==> Formula    % a premise
          | Goal                   % the conclusion
```

- **A property is a fact** of the program, `pred property o:string,
  o:(pred)` (declared in [`lib/property.elpi`](lib/property.elpi)).  It is
  written next to the predicate it is about and **type checked by Elpi with
  the program**: a property that mentions a predicate with the wrong
  arguments is a compile error, not a silent test of nothing.  The program
  runs as before with `elpi -I elpi-tools/check/lib`: the facts are inert.
- **The formula is λProlog's own logic**: `pi` for "for all", `==>` (Elpi
  4's implication, right associative) for "implies".  The reading is the
  logical one, ∀L R L2. rev L R ⊃ rev R L2 ⊃ L2 = L; elpi-check does not run
  the formula as a goal (that would *assume* `rev L R`), it interprets it:
  the premises are run, the conclusion is checked for each of their
  solutions.  `,` cannot separate premises (`a, b ==> c` reads
  `a, (b ==> c)` in Elpi 4): write `a ==> b ==> c`.
- **Inputs and outputs come from the modes** that Elpi 4 declares.  Reading
  the premises left to right, a variable first met in an output argument
  (`R` in `rev L R`, `func rev list A -> list A`) is **computed** by that
  premise, never generated: generating `R` at random would make the premise
  false almost always.  A variable first met in an input argument, or only
  in the conclusion, is **generated** from its type.  So the formula can
  quantify every variable, as the logical statement does.
- **Types** are inferred from the signatures of the predicates and the
  types of the constructors (`L : list A`); a type parameter left open is
  taken as `int`, as QuickCheck defaults a polymorphic property.  A type
  can be written: `pi L : list string \ ...`.
- **`generated-by G`** (a premise) asks for **guided generation**: the
  variables of `G` are produced by solving `G` with random choices among
  its rules (the interpreter of [`../debug`](../debug/README.md) with a
  random strategy), so they satisfy `G` by
  construction.  This is for premises that random values rarely satisfy,
  typically a typing relation: `pi M T N\ generated-by (of M T) ==> step M N
  ==> of N T` tests preservation on well-typed terms only.  It is the idea of
  Blanco, Miller and Momigliano (LFMTP 2017, PPDP 2019): the test data come
  out of a random derivation of the generator predicate; here a
  depth-bounded random meta-interpreter on the reflected rules, not their
  proof certificates.  Run as a goal, `generated-by G` is `G`.

Precedent: Ciao Prolog states assertions in the program and checks some of
them by test generation; we have not compared the details.

## How a property is tested

The program is read as data by [`../reflect`](../reflect/README.md) (its
types, constructors, signatures with modes, rules), together with the
declarations of Elpi's builtins (`list`, `pair`, `option`, `bool`, the
signatures of `std.*`).  Everything else is Elpi, in [`lib/`](lib):

| file | what |
|---|---|
| [`analyse.elpi`](lib/analyse.elpi) | variables of a property: type, generated or computed |
| [`generate.elpi`](lib/generate.elpi) | random terms of a type, size-controlled, binders included |
| [`shrink.elpi`](lib/shrink.elpi) | smaller candidates of a value |
| [`run.elpi`](lib/run.elpi) | tests, shrinking, report |
| [`goals.elpi`](lib/goals.elpi), [`types.elpi`](lib/types.elpi), [`random.elpi`](lib/random.elpi) | helpers |

A test at size S: the generated variables get random values; the
`generated-by` premises are solved at random (depth S); the test is
**discarded** if the premises have no solution, **fails** if a solution of
the premises falsifies the conclusion, **passes** otherwise.  S grows from 1
to `-size` along the tests, so small cases come first.

**The distribution** (the weak point of naive random generation, as
Blanco, Miller and Momigliano found):

- a value is built from the constructors of its type with a budget S: the
  recursive structure (spine of a list, nodes of a tree) has at most S
  constructors, leaves are preferred with probability 1/S.  Measured: the
  length of a list generated with budget 10 is uniform on 0..9 (2000
  samples: between 188 and 223 per length);
- binders: an argument of type `tm -> tm` is generated under `pi x\` with
  `x` as a leaf, so closed λ-terms such as `lam x\ app x (lam y\ x)` come
  out directly;
- the report gives the number of discarded tests and the average size of the
  values of the passed tests, so a premise that filters out all but the tiny
  cases shows: in [`tests/sort.elpi`](tests/sort.elpi), `sorted L ==> ...`
  discards 65 of 100 random lists and the tests that pass have an average
  size of 4, against 12 for the same property without the premise.  The
  remedy is `generated-by` with a generator predicate.

**Shrinking** is greedy: a value is replaced by a smaller candidate
(a leaf of its type, a subterm of the same type, a binder body that does not
use its variable, one argument shrunk; 0, N/2, N-1 for an int) as long as
the test still fails; values produced by `generated-by` are shrunk too, the
premise is then checked natively.  Example (`short-lists` in
[`tests/sort.elpi`](tests/sort.elpi)): `[-6, -4, -1, -5, 1, 0, 2, -1]` is
shrunk in 7 steps to `[0, 0, 0, 0, 0, 0, 0, 0]`.  It changes one variable at
a time, so it can stop at a local minimum (`X = -1, L = [-1]` where
`X = 0, L = [0]` also fails).

## Examples and tests

[`tests/`](tests): `dune build @runtest` checks the reports against
`*.expected` (seed 1).

- [`rev.elpi`](tests/rev.elpi): reverse and append; two true properties and
  a false one.
- [`sort.elpi`](tests/sort.elpi): insertion in a sorted list; a premise that
  discards, a bug found and shrunk, a long counterexample shrunk.
- [`stlc.elpi`](tests/stlc.elpi): the simply typed λ-calculus in HOAS
  (binders are Elpi lambdas, the typing context is `pi x\ of x A => ..`).
  Preservation holds on terms generated by `generated-by (of M T)`; with a
  wrong reduction rule it fails, counterexample `app (lam x\ c) (lam x\ c)`
  shrunk to `app (lam x\ c) c`; substitution with a generated binder
  `F : tm -> tm`; `copy` on terms generated from their type; a `pi` in the
  conclusion; a false property on all closed terms.

Measured on this (shared) laptop, two runs each: 0.3 s to read and compile
the program and the checker; with 100 tests per property rev 1.3-1.5 s (3
properties), sort 1.2 s (4), stlc 2.9-3.8 s (6) with the checker's former solver and
8.5-13 s with the interpreter of elpi-tools/debug (2-3 times slower, measured
2026-11-18 on a loaded laptop; same reports); with 1000 tests rev
9.8-10.4 s, sort 7.4 s, stlc 15-16.5 s, at most 95 MB of memory.

## Limits (said plainly)

- No time bound per test: a premise or conclusion that loops makes the run
  loop; a runtime error in the program (e.g. `is` on an unbound variable,
  `std.fatal-error`) stops the whole run.
- The random solver (elpi-tools/debug with options random-order,
  first-solution, max-depth, ignore-cut) ignores cuts and keeps the first
  solution of each subgoal; a hypothesis shares its variables (`pi x\ of x
  A => ..` works) and its own universally quantified variables get fresh
  ones.  A generator predicate whose rules need ground inputs (e.g.
  `X =< Y` on unbound integers) raises a runtime error.
- A conjunction has at most 10 conjuncts where the checker looks into it
  (Elpi represents it as one node; there is a pattern per length).
- Values of predicate type (`(pred ..)`) cannot be generated.
- No spilling `{ }` inside a property formula (it is data).
- No exhaustive enumeration of small values (SmallCheck style), no
  checking of the properties at run time on a real execution (that needs
  the meta-interpreter of the debugger, section 6 of the design notes).
