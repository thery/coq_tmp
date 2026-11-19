# elpi-tools: design

This document describes the design of elpi-tools: what each tool does, how
it is implemented, and the reasons for the main choices.  It is intended
for developers of Elpi and of tools built on it.  The tools target
standalone Elpi 4.0.0 (opam switch `elpi5`), not Rocq-Elpi.  All outputs
shown were produced by the tools in this repository; absolute paths are
shortened to the file name, and long lines are cut and marked `…`.

## Overview

Four tools, each a directory with its own README, all built by one
`dune build` in `elpi-tools/`:

| tool | what it does | written in | page |
|---|---|---|---|
| [`reflect/`](reflect/README.md), `elpi-reflect` | prints a program (its types, signatures with modes, rules, CHR rules) as Elpi facts, so that a tool written in Elpi can read it | OCaml, on Elpi's parser | [design/reflect.md](design/reflect.md) |
| [`check/`](check/README.md), `elpi-check` | QuickCheck for Elpi: properties stated in the program, tested on random values, counterexamples shrunk | Elpi (+ a small OCaml driver) | [design/check.md](design/check.md) |
| [`debug/`](debug/README.md), `elpi-debug` | a debugger: ports, unify steps with their bindings, `pi`/`=>`, the cut, CHR at work, explained failures, interactive stepping, a JSON channel for front ends | Elpi, a meta-interpreter (+ an OCaml driver) | [design/debug.md](design/debug.md) |
| [`dap/`](dap/README.md), `elpi-dap` + `dap/vscode` | VS Code: a debug adapter on `elpi-debug -machine`, and the properties of elpi-check in the Test Explorer | OCaml, JavaScript | [design/dap.md](design/dap.md) |

How they fit together:

```
                 program.elpi
                      │  parsed by Elpi's own parser
                      ▼
               ┌─────────────┐   facts: reflect.clause, reflect.signature,
               │ elpi-reflect│   reflect.chr-rule, reflect.premises …
               └──────┬──────┘
          ┌───────────┴────────────┐
          ▼                        ▼
   ┌─────────────┐  debug.run  ┌─────────────┐  -machine   ┌──────────┐   DAP   ┌─────────┐
   │ elpi-check  │────────────▶│ elpi-debug  │◀───────────▶│ elpi-dap │◀───────▶│ VS Code │
   │ (properties)│ random      │ (meta-      │ JSON lines  │ (adapter)│         │         │
   └──────┬──────┘ strategy    │ interpreter)│ + commands  └──────────┘         └────┬────┘
          │ -json report      └─────────────┘                                      │
          └───────────────────────────────────────────▶ Test Explorer ─────────────┘
                                                        ("Debug this counterexample":
                                                         the replay goal under elpi-debug)
```

The one idea behind all of them: **the program as data, interpreted by
Elpi itself**.  Elpi has no `clause/2`, so elpi-reflect gives the rules
as facts; the debugger is a meta-interpreter over those facts; the
property checker generates values from the declared types and modes, and
solves `generated-by` premises with the same meta-interpreter under a
random strategy; the VS Code part only drives the debugger and the
checker as child processes.

The main choices, each argued in its page:

- **A meta-interpreter, not an instrumented runtime** (debug): the debugger
  runs on an unmodified Elpi, can stop, retry, explain, and change the
  strategy (random, depth bound, cut ignored) — at a cost of about 20 times
  the native time, measured.
- **Clauses compiled once into local clauses** that Elpi itself indexes
  and matches (debug): 3 to 4 times faster than interpreting a body at each
  call.
- **The connectives stay native** (debug): the cut is Elpi's own cut, `pi`
  and `=>` are Elpi's, so their semantics are not reimplemented.
- **CHR at depth 1** (debug): the CHR rules run natively; the debugger
  shows their attempts and runs their goals.
- **Modes decide what is generated** (check): a variable first met in an
  output is computed by its premise, never generated.

Where Elpi lacks something, the tools carry a **stand-in** behind a
small interface, and each one is an item of
[`debug/ELPI-FEATURE-REQUESTS.md`](debug/ELPI-FEATURE-REQUESTS.md) (summary below).

## The parts

1. [**reflect**: the program as data](design/reflect.md)
2. [**check**: properties, generation, shrinking, the replay goal](design/check.md)
3. [**debug**: the meta-interpreter](design/debug.md) — compiled clauses,
   the box and its ports, unify events and the trail interface, λProlog
   (`pi`, `=>`, eigenvariables, pruning), the cut, builtins and bridges,
   CHR at depth 1, the explanation of failures, the stepper, `-machine`
4. [**dap**: VS Code](design/dap.md) — the adapter, the extension, the
   Test Explorer

## Requested features of Elpi, in short

[`debug/ELPI-FEATURE-REQUESTS.md`](debug/ELPI-FEATURE-REQUESTS.md) gives, for each item,
the API (signature), its contract, where it would be used
(file:predicate) and what would go away.  In order of benefit:

| # | feature | kind | stand-in today |
|---|---|---|---|
| 1 | `vars-of`: the variables of a term | feature | a walk in Elpi, blind inside builtin applications; reflect's `-closed` |
| 2 | `uuid` of a variable, and a printer that uses it | feature | the number of Elpi's printer, regexps on its text |
| 3 | the trail: `trail-mark`, `bindings-since` | feature | a snapshot of the variables in reach, compared |
| 4 | CHR: a rule's goal run in the current program | feature | a runner goal suspended at the start, fed through CHR |
| 5 | CHR: an event per rule attempt and outcome | feature | every guard rewritten, notes on an OCaml queue |
| 6 | CHR: the identity of a suspension, the store from Elpi | feature | a number hidden in the context of each constraint |
| 7 | LPCIC/elpi#505 | bug fix | bridges as static rules, a first run to write them |
| 8 | API: compile parsed units | feature | one `Obj.magic` |
| 9 | take a goal apart (conjunction, builtin, λ) | feature | one pattern per arity up to 16 |
| 10 | `catch`/`throw` | feature | retry unwinds by failing every event |
| 11 | the scope of a variable | feature | a trial binding per eigenvariable |
| 12 | the rules of a program as data | feature | elpi-reflect's copy of the compiler's front end |
| 13 | `:nooc` for local clauses | feature | compiled clauses shaped to avoid the occurs check |
| 14 | locations with end line; CHR rule location | feature / bug? | files read again |
| 15 | the names of the query variables | feature | a second parse of the goal |
| 16 | `names` documentation | doc fix | — |

## Running the tests

```sh
eval $(opam env --switch=elpi5)       # Elpi 4.0.0, yojson
cd elpi-tools
dune build @runtest                   # reflect, check, debug, dap (and the
                                      # extension's tests when node is installed)
dune promote                          # accept a new output of a cram test
```

Each part's tests: `reflect/tests/*.expected`, `check/tests/*.expected`
and `check/tests/json.t`, `debug/tests/*.t` (cram: traces, explanations,
interactive sessions, `-machine`), `dap/tests/*.t` (scripted DAP sessions)
and `dap/vscode/test` (Node).  Benchmarks, not run by the tests:
`debug/tests/bench.elpi`, `debug/tests/chrbench.elpi`.  To try the tools
by hand:

```sh
dune exec -- elpi-reflect debug/tests/append.elpi
dune exec -- elpi-check -I check/lib demo/lists.elpi
dune exec -- elpi-debug -trace debug/tests/append.elpi 'rev [1,2] R'
dune exec -- elpi-debug -i debug/tests/lambda.elpi 'of (lam x\ lam y\ x) T'
```
