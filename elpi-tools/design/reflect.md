# reflect: the program as data

[← overview](../DESIGN.md) · README: [`../reflect/README.md`](../reflect/README.md)

## What

`elpi-reflect FILE` prints the program FILE as Elpi facts: its data types,
constructors, predicate signatures **with their modes**, rules (head and
body as ordinary terms), the places of the goals of each body, and its
CHR rules.  A tool written in Elpi accumulates the format
([`reflect.elpi`](../reflect/reflect.elpi)), the program itself and the
facts, and reads the program by querying them.

On [`examples/shapes.elpi`](examples/shapes.elpi) (a namespace, a spill,
a binder, a CHR rule):

```elpi
namespace geo {
  func area shape -> int.
  ...
  func total list shape -> int.
  total [] 0.
  total [S | Ss] T :- T is {area S} + {total Ss}.
}
pred apply-all i:(int -> shape), o:list shape.
apply-all F [X, Y] :- pi n\ X = F 1, Y = F 2.
constraint small {
  rule (small X) | (X > 10) <=> fail.
}
```

```
$ elpi-reflect design/examples/shapes.elpi        # paths shortened
reflect.signature "geo.total" geo.total reflect.functional [(reflect.arg reflect.in (reflect.tcon "list" [(reflect.tcon "shape" [])])), (reflect.arg reflect.out (reflect.tcon "int" []))] ff (reflect.srcloc "shapes.elpi" 11 2).
…
reflect.clause geo.total 2 (reflect.srcloc "shapes.elpi" 13 2) [(reflect.binders [])] (geo.total [S | Ss] T) ((geo.area S Spill_1), (geo.total Ss Spill_2), (T is (Spill_1 + Spill_2))).
reflect.premises (reflect.srcloc "shapes.elpi" 13 2) [(reflect.span "shapes.elpi" 13 28 13 34), (reflect.span "shapes.elpi" 13 39 13 47), (reflect.span "shapes.elpi" 13 22 13 48)].
reflect.clause apply-all 1 (reflect.srcloc "shapes.elpi" 18 0) [(reflect.binders [(reflect.binder "n" none)])] (apply-all F [X, Y]) (pi n\ ((X = (F 1)), (Y = (F 2)))).
…
reflect.chr-rule 1 (reflect.srcloc "shapes.elpi" 21 7) [] [small] [(reflect.sequent _ _ (small X))] [] (some (X > 10)) (some (reflect.sequent _ _ fail)).
```

Note what was resolved: `total` inside `namespace geo` is `geo.total`;
the spills `{area S}` and `{total Ss}` became `Spill_1`, `Spill_2` and
two goals placed before the goal that held them (and their places,
`reflect.premises`, point inside the braces); the `pi n\` binder is an
Elpi λ, its source name kept in the attribute `binders`.  With `-closed`,
each rule is also given under one binder per variable:

```
$ elpi-reflect -closed debug/tests/append.elpi | grep closed-clause
reflect.closed-clause 1 (L\ reflect.clause append 1 (reflect.srcloc "append.elpi" 5 0) [(reflect.binders [])] (append [] L L) true).
reflect.closed-clause 4 (X\ L\ M\ R\ reflect.clause append 2 (reflect.srcloc "append.elpi" 6 0) [(reflect.binders [])] (append [X | L] M [X | R]) (append L M R)).
```

## How

An OCaml program on the `elpi` library ([`lib/`](../reflect/lib)):

1. parse with Elpi's own parser (`Elpi_parser`), accumulated files
   included;
2. resolve names as the compiler does ([`scope.ml`](../reflect/lib/scope.ml):
   namespaces, `shorten`, `.name` escapes), desugar spilling
   ([`spill.ml`](../reflect/lib/spill.ml)), apply `:before`, `:after`,
   `:replace`, `:remove`, `:if` to get Elpi's order of the rules
   (`reflect.ml:place_rules`);
3. print each declaration as a fact ([`print.ml`](../reflect/lib/print.ml)):
   the program's constants appear as themselves (`geo.total`), so the facts
   are **type checked with the program**, and `reflect.clause geo.total _ _
   _ H B` is indexed by the predicate.

A tool reads a rule with fresh variables at each lookup, as `clause/2`
would (`debug/lib/program.elpi:program-rule`):

```elpi
program-rule P I Head Body (at Loc Attrs) :-
  reflect.clause P I Loc Attrs Head Body,
  constant Head Q _, same_term Q P.     % (the rules of an overloaded predicate have no index)
```

Two constructs of heads cannot be data (in a fact they would match
instead of being returned): `uvar` and `P as X` become
`reflect.uvar-pattern` and `reflect.as-pattern P X`.

## Why this way

- **Why outside Elpi.**  Elpi has no builtin that gives the rules of the
  running program (Prolog's `clause/2`).  Reading the source again is the
  only way today; doing it with Elpi's parser keeps the syntax exact.
  The cost is a copy of the compiler's front end (scoping, spilling,
  order: about 350 lines) and its limits (macros, a spill under a λ inside
  an atom, `:autospill`: README, "Not supported").  Requested feature 12 asks
  for the rules of a compiled program instead.
- **Why facts and not a term "the program".**  Facts are indexed by Elpi
  (the rules of one predicate only), give fresh variables at each lookup,
  and are type checked with the program: a tool cannot misread a rule.
- **Why modes in the signatures.**  Elpi 4 declares them (`func`, `pred
  i:/o:`); elpi-check uses them to tell generated from computed
  variables, elpi-debug to match inputs and unify outputs as Elpi does.
- **Why `-closed`.**  Elpi code cannot find the variables of a term inside
  an application of a builtin (`X is Y + 1` is one node), so the debugger
  cannot close a rule itself; elpi-reflect, which sees the source, can.
  It goes with `vars-of` (requested feature 1).
- **Why `premises` with spans.**  The debugger shows which goal of a body
  a call comes from (`(premise 2 of append.elpi:15)`) and VS Code
  highlights it.  Elpi's locations give the end of a term as an offset,
  not a line: elpi-reflect reads the file again to find it (list of requested features
  item 14).
