# debug: the meta-interpreter

[← overview](../DESIGN.md) · README: [`../debug/README.md`](../debug/README.md)

## What

`elpi-debug FILE GOAL` runs GOAL by interpreting the rules of FILE and
shows what the real engine does not: the four ports of each call, the
unify step of the selected clause with the bindings it makes, the goal of
the body a call comes from, `pi` and `=>`, the cut, the suspension and
resumption of goals by CHR and the attempts of the CHR rules, and on
failure an explanation.  On [`../debug/tests/append.elpi`](../debug/tests/append.elpi):

```
$ elpi-debug -trace append.elpi 'rev [1,2] R'
Call: #1 rev [1, 2] X0
Unify: #1 with append.elpi:15: rev [1, 2] X0
  Call: #2 rev [2] X1   (premise 1 of append.elpi:15)
  Unify: #2 with append.elpi:15: rev [2] X1
    Call: #3 rev [] X2   (premise 1 of append.elpi:15)
    Unify: #3 with append.elpi:14: rev [] []
      X2 := []
    Exit: #3 rev [] []
      X2 := []
    Call: #4 append [] [2] X1   (premise 2 of append.elpi:15)
…
  Exit: #5 append [2] [1] [2, 1]
      X0 := [2, 1]
Exit: #1 rev [1, 2] [2, 1]
      X0 := [2, 1]
Solution 1:
  R = [2, 1]
```

Options: `-trace`, `-builtins`, `-break P`, `-i` (interactive), `-machine`
(for front ends), `-profile`, `-compare` (native and interpreted answers
must agree), and a strategy (`-random SEED`, `-first`, `-max-depth N`,
`-ignore-cut`) used by elpi-check.

## How: the pieces

The interpreter is [`../debug/lib/*.elpi`](../debug/lib), concatenated by
dune into `debug.elpi` in one `namespace debug { }`.  The driver
([`../debug/bin/elpi_debug_main.ml`](../debug/bin/elpi_debug_main.ml))
compiles one program of six units:

```
 1 reflect.elpi       the format of the facts
 2 debug.elpi         the interpreter
 3 FILE without its rules   declarations (so terms type check) and CHR rules (run natively, rewritten)
 4 the facts          elpi-reflect -closed FILE
 5 the bridges        one native rule per predicate of FILE, back into the interpreter
 6 driver clauses     the builtins of the driver: pause, CHR notes, the store
```

and runs `debug.run Options Goal` ([`interpreter.elpi:run`](../debug/lib/interpreter.elpi)).

### From a call to a unify event

```
  goal G of a clause body                         (compiled once: [compile])
        │  debug.call Ctx P G Entry
        ▼
  ┌─ call ──────────── box #Id ─────────────────────────────┐
  │  call port  ── mark of the trail (if shown)             │
  │  backchain  ── ordered-clause G Id Ctx                  │
  │       │        Elpi itself selects the local clauses    │
  │       ▼        "compiled G Key Id Ctx" whose head        │
  │  compiled clause:   matches G (its indexing, :index(2)) │
  │    rest of the head: inputs matched, outputs unified    │
  │    unify port  ── bindings since the mark               │
  │    the body of the rule, compiled (native connectives)  │
  │  exit port  ── bindings of the whole call               │
  └─────────────────────────────────────────────────────────┘
```

**Clauses compiled once into local clauses**
([`compiled.elpi`](../debug/lib/compiled.elpi)).  At the start of `run`
every rule (from its closed form) becomes a local clause of `compiled`;
`=>` compiles its hypothetical clauses the same way.  The head of the
compiled clause is the head of the rule up to its first argument that
needs more than matching, so **Elpi selects the candidates and matches
them** natively; the clause body does the rest of the head, the unify
event and the compiled body (`compiled.elpi:clause-with`):

```elpi
clause-with Key Origin Names H B P Prefix Modes Rest Vs
    (pi id\ pi ctx\ compiled G Key id ctx :- Body id ctx) :-
  std.append Prefix Vs Args, mk-app P Args G,
  rest-goals Modes Vs Rest Gs,
  pi id\ pi ctx\ clause-body id ctx Origin Names H B Gs (Body id ctx).
```

*Why*: measured on [`../debug/tests/bench.elpi`](../debug/tests/bench.elpi)
(README, Cost), compiling a body at each call and matching heads argument
by argument cost `count 6400` 0.52 s; compiled clauses 0.19 s.  A
compiled clause returns nothing: Elpi makes the occurs check on the head
of every local clause, so returning a term that holds the goal walked
it (a first version was quadratic: 4.5 s; requested feature 13).

### The box and its ports

```
            ┌──────────────────────────┐
   call ───▶│                          │───▶ exit
            │   backchain: the clauses │
   fail ◀───│   of the goal            │◀─── redo
            └──────────────────────────┘
```

[`interpreter.elpi:box-ports`](../debug/lib/interpreter.elpi) — the redo
port is a clause tried only when backtracking comes back into a call
that has exited; it shows the port and fails into the choice points
left inside:

```elpi
box-ports Exited Box :-
  call-port-marked Box Mark, solutions-from Mark Box, stash_in_safe Exited "exited", exit-or-redo Mark Box.
box-ports Exited Box :-
  port fail-port Box, note-failure-if-first Exited Box, fail.

exit-or-redo Mark Box :- exit-port-with-bindings Mark Box.
exit-or-redo _ Box :- port redo-port Box, fail.
```

The safe `Exited` survives backtracking: a call that fails without ever
exiting is a candidate for the explanation.  On the fast path (no option)
the box is only its solutions (`unseen-box`): no port, no choice point
for retry.

### Unify events and the trail interface

The bindings of a unify step (`X0 := [2 | X3]`) and of a whole call (at
its exit) come from two primitives of
[`primitives.elpi`](../debug/lib/primitives.elpi): `trail-mark G M`
before, `bindings-since M Bs` after.  Today they are stand-ins (a snapshot
of the variables in reach of G, compared later); Elpi's trail would make
them exact and cheap (requested feature 3).  The pruning Elpi does is
reported:

```
$ elpi-debug -trace lambda.elpi 'pi x\ pi y\ same (G x) (F x y)'
Pi: x#1 is a new eigenvariable; its scope: pi c1 \ same X0 (X1 x#1 c1)
Pi: x#2 is a new eigenvariable; its scope: same X0 (X1 x#1 x#2)
Call: #1 same X0 (X1 x#1 x#2)
Unify: #1 with lambda.elpi:22: same (X3 x#1) (X3 x#1)
      X2 := c2 \ X3 c2
      X1 := c2 \ c3 \ X3 c2   (pruned: X3 gets 1 of the 2 arguments)
…
Solution 1:
  F = c0 \ c1 \ X3 c0
  G = c0 \ X3 c0
```

(`X0` shows as `X2` at the unify step: the stand-in of `vars-of` renames
a variable kept by Elpi in compact form, `G x`; requested features 1-2.)

### λProlog: pi, =>, eigenvariables

`pi` and `=>` stay native: the compiled body of `pi x\ B` is, schematically, `pi x\ (port,
eigen x Name => B')`, so the eigenvariable is Elpi's own and is shown by
its source name (`x#1`); `=>` adds the hypothetical clauses as data
(`hyp P Origin C`) and compiled, with Elpi's own scope:

```
$ elpi-debug -trace lambda.elpi 'of (lam x\ lam y\ x) T'
Call: #1 of (lam c0 \ lam c1 \ c0) X0
Unify: #1 with lambda.elpi:14: of (lam c0 \ lam c1 \ c0) (arr X1 X2)
      X0 := arr X1 X2
  Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of (lam c1 \ x#1) X2
  Assume: of x#1 X1   (added to the local program, for of (lam c1 \ x#1) X2 only)
  Call: #2 of (lam c1 \ x#1) X2   (premise 1 of lambda.elpi:14)
…
    Call: #3 of x#1 X4   (premise 1 of lambda.elpi:14)
    Unify: #3 with hypothesis added by #1: of x#1 X1
      X4 := X1
…
Solution 1:
  T = arr X1 (arr X3 X1)
```

### The cut

The classic difficulty: a cut in a body must discard the other clauses of
the goal and the choice points before it, which belong to the
interpreter, and Elpi has no "cut to here".  The answer: a body is
**compiled into a native goal** where the connectives and the cut stay
native ([`interpreter.elpi:compile`](../debug/lib/interpreter.elpi)):

```elpi
compile Ctx _ Ns ! (debug.cut-port Ctx, !) Ns :- !.
compile Ctx E Ns G Code Ns1 :- conjuncts G Gs, !, compile-all Ctx E Ns Gs Codes Ns1, mk-conj Codes Code.
```

The compiled body is the body of the compiled clause, so its native cut
discards exactly the other candidates of the goal: Elpi's semantics, for
free, through `pi`, `sigma`, `=>`, local to `;`.

```
$ elpi-debug -trace cut.elpi 'first 1 [0,3,5] X'
…
  Exit: #2 mem 3 [0, 3, 5]
      X0 := 3
Cut: #1 commits to its current clause
Exit: #1 first 1 [0, 3, 5] 3
```

Limit: a cut through a variable (`G = !, …, G`) cuts only G.

### Builtins and bridges

A builtin runs natively, with its ports.  But native code may call the
program back (`std.map L p`, `not (p X)`, a goal woken by CHR), and the
program's rules are not in Elpi's program (unit 3 has none).  Hence one
**bridge** per predicate (unit 5, [`program.elpi`](../debug/lib/program.elpi)):

```
 interpreter ── native Ctx Entry (std.map L p) ──▶ Elpi runs std.map
                  (current-ctx Entry Ctx => G)            │ calls p X
                                                          ▼
 interpreter ◀── debug.bridge (p X) ◀── bridge rule:  p X0 :- !, debug.bridge (p X0).
   call Ctx p (p X) Entry   (the context of the innermost builtin)
```

```elpi
run-native Ctx Entry G :- (current-ctx Entry Ctx => G).                 % natives.elpi
bridge G :- current-ctx Entry Ctx, !, program-goal G P, call Ctx P G Entry.
```

The bridges are static rules written by a first run of the driver,
because as local clauses `pi x1..xn\ …` they crash Elpi when a CHR rule
fires (LPCIC/elpi#505, requested feature 7).

### CHR at depth 1, and its view

The CHR rules of FILE run **natively** (Elpi matches them, runs the
guards, removes constraints); `declare_constraint` is the real one; a
woken goal comes back through its bridge and enters by a resume port.
The driver rewrites each rule ([`bin/chr_in_view.ml`](../debug/bin/chr_in_view.ml))
so that the interpreter sees it at work:

```
$ elpi-debug -trace leq.elpi 'leq A B, leq B C, leq C A'
…
  Delay: [S2] leq X1 X2 on [X1, X2]
  Rule: clause 7 leq.elpi:7 tried on [S2]
  Rule: clause 7 leq.elpi:7 guard fails
  Rule: clause 9 leq.elpi:9 tried on [S1, S2]
  Rule: clause 9 leq.elpi:9 fires
Call: #3 leq X0 X2   (goal of the CHR rule at leq.elpi:9)
…
  Rule: clause 8 leq.elpi:8 tried on [S4, S3]
  Rule: clause 8 leq.elpi:8 fires, removes [S4, S3]
  Resume: [S2] #5 leq X1 X0
…
Solution 1:
  A = X0
  B = X0
  C = X0
```

Three stand-ins ([`lib/chr-hooks.elpi`](../debug/lib/chr-hooks.elpi),
requested features 4-6):

- *attempts*: each guard G becomes `rule-tried Loc Kept Contexts, G,
  rule-guard-held`; a guard runs in a runtime of its own with the static
  program, so the notes go to an OCaml queue of the driver, read after
  the propagation;
- *suspension numbers*: `delay` declares the constraint under the clause
  `suspended-as K`, and the driver adds `suspended-as` to the context
  filter of each constraint block, so the context carries `[S2]`;
- *the goal of a rule*: Elpi runs it with the static program, where the
  interpreter's local clauses are missing; it is handed to a **runner**:

```
 start of run:  declare_constraint (rule-runner T) [T, _]     (suspended under run's local clauses)
 a rule fires:  its goal N, rewritten  hand-rule-goal Loc N
                  └─ declare_constraint (rule-goal-request Loc N) [_]
 CHR:   rule (rule-runner T) \ (rule-goal-request Loc G) <=> (T = run-goal Loc G).
 T bound ─▶ the runner wakes, with the program of run: it suspends itself
            again and runs  run-rule-goal Loc G  in the interpreter
```

*Why depth 1*: interpreting CHR would reimplement Elpi's matching,
guards and propagation; running them natively keeps the semantics, and
`-compare` checks the answers against the real engine on the tests.

### The explanation of a failure

At the fail port of a call that never exited, the goal is back as it was
called: each candidate clause is tried again and the reason it does not
apply is computed ([`explain.elpi`](../debug/lib/explain.elpi)): the
smallest clashing subterms, an input that the goal leaves unknown, the
occurs check, an eigenvariable out of scope, no clause at all.

```
$ elpi-debug append.elpi 'append X [2] [1,2]'
debug: no (more) solution.
Deepest failure (depth 0): #1 append X1 [2] [1, 2]
  clauses tried:
    append.elpi:5: append [] X0 X0
        does not match: argument 1 (input): X1 vs [] (the goal has a variable where the clause expects a term: an input argument is only matched)
    append.elpi:6: append [X2 | X3] X4 [X2 | X5]
        does not match: argument 1 (input): X1 vs [X2 | X3] (the goal has a variable where the clause expects a term: an input argument is only matched)
No solution.
```

### The stepper, and retry

`-i` stops at each event and reads a command (creep, skip, leap, out,
retry, fail, print, scope, hyps, store, breakpoints):

```
$ printf 'c\nc\nc\nc\nc\nr\nc\nn\n' | elpi-debug -i -echo append.elpi 'rev [1,2] R'
…
    Unify: #3 with append.elpi:14: rev [] []
      X2 := []
   ? r
    retry #3: back to its call port
    Call: #3 rev [] X2   (premise 1 of append.elpi:15)
   ? c
…
```

Retry: each call runs under `attempt`, whose second clause is a choice
point before the call port; `r` records the request in a safe and fails,
every event fails while it is pending, and the second clause of `attempt`
for that call takes it and runs the call again.  The bindings, the local
program and the eigenvariables go back with backtracking, since `=>` and
`pi` are Elpi's own.  A `catch`/`throw` would make it immediate
(requested feature 10; [`stepper.elpi`](../debug/lib/stepper.elpi), section
Unwinding).

### `-machine`: the channel for front ends

With `-machine`, besides its text, elpi-debug prints the listing of the
program and, at each stop, a JSON description, then reads a command:

```
$ printf 'c\nn\n' | elpi-debug -machine append.elpi 'append [1] [2] L' | cut -c1-120    # paths shortened first
@@elpi-debug {"event":"program","clauses":[{"clause":1,"predicate":"append","file":"append.elpi","line":5},{"clause":2,"
@@elpi-debug {"event":"stop","stop":1,"reason":"start","port":"Start","text":"Start: the run is about to start","frames"
Call: #1 append [1] [2] X0
@@elpi-debug {"event":"stop","stop":2,"reason":"step","port":"Call","text":"Call: #1 append [1] [2] X0","frames":[{"id":
Solution 1:
  L = [1, 2]
```

A stop gives the stack (each call with its clause, its premise and its
place, its arguments with modes, the scope of its variables), the
bindings of the step, the local program, the eigenvariables, the query
variables by name, the store ([`machine.elpi`](../debug/lib/machine.elpi)).
A pause is the signal SIGUSR1: the interpreter asks the driver at each
event.

## Cost

From the README (2026-11-19, a loaded laptop, the minimum of 10 runs):

| goal | native | interpreted | ratio |
|---|---|---|---|
| `count 6400` | 0.007 s | 0.15 s | ~22 |
| `bench 200` (naive reverse, 20 000 calls) | 0.014 s | 0.30 s | ~22 |
| `queens 8 Q` | 0.005 s | 0.10 s | ~21 |

## Why a meta-interpreter

- **The alternative: instrument Elpi's runtime** (its tracer exists, and
  elpi-lang has a trace viewer).  It would be faster, but it shows a run
  after the fact; stepping, retry, breakpoints, the explanation and a
  random strategy would all need changes in Elpi's core.  A
  meta-interpreter runs on an unmodified Elpi, and its strategy is data
  (`strategy Order Solutions Depth Cut`), which elpi-check reuses.
- **The price** is about 20 times the native time, and the stand-ins
  where Elpi code cannot see what the runtime knows (the variables of a
  term, their identity, the trail, CHR's attempts): each one is an item
  of [`../debug/ELPI-FEATURE-REQUESTS.md`](../debug/ELPI-FEATURE-REQUESTS.md).
- **What is kept native, and why**: connectives (the cut's semantics),
  `pi`/`=>` (scopes, restored by backtracking), head matching and clause
  selection (Elpi's indexing), builtins, CHR (its matching and
  propagation).  What is interpreted is only what must be seen: the
  calls of the program and their clauses.
