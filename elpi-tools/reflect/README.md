# elpi-reflect: an Elpi program as Elpi data

How it works and why, with the other tools: [`../DESIGN.md`](../DESIGN.md) (this part: [`../design/reflect.md`](../design/reflect.md)).

Elpi has no builtin that returns the rules of the running program (Prolog's
`clause/2`).  `elpi-reflect` fills the gap from outside (the API that would make it
unnecessary is item 12 of the list of requested features for Elpi,
[`../debug/ELPI-FEATURE-REQUESTS.md`](../debug/ELPI-FEATURE-REQUESTS.md)): an OCaml program
on the `elpi` library reads `.elpi` files with Elpi's own parser and prints
their declarations, rules and CHR rules as **Elpi facts**.  A tool written
in Elpi (a meta-interpreter, a debugger, the property checker
[`../check`](../check/README.md)) then accumulates three files:

1. [`reflect.elpi`](reflect.elpi): the declarations of the format below;
2. the user's program;
3. the facts printed by `elpi-reflect user.elpi`;

and reads the program by querying the facts.  The facts mention the
program's own constants (`rev`, `app`, …), so they are type checked with the
program and a rule's head and body are ordinary goals that can be run.

    elpi-reflect [-I DIR].. [-D VAR].. [-builtins] [-closed] FILE..     # facts on standard output

With `-builtins` it also prints the declarations (data types, constructors,
signatures; not the rules) of Elpi's builtins and standard library, e.g.
the signature of `std.rev`.  With `-closed` it also prints each rule
closed, its variables bound: `closed-clause` below (elpi-debug and
elpi-check use it).

Standalone Elpi 4 only, not Rocq-Elpi.

## The format

All names live in the namespace `reflect`.  Excerpt of
[`reflect.elpi`](reflect.elpi):

```elpi
symb srcloc string -> int -> int -> srcloc.      % file, line (from 1), column (from 0)
symb span string -> int -> int -> int -> int -> span.   % file, line, column, end line, end column

symb tcon string -> list ty -> ty.               % int = tcon "int" [], list A = tcon "list" [A]
symb tarrow ty -> ty -> ty.                      % A -> B
symb tpred functionality -> list arg -> ty.      % (pred i:A, o:B), (func A -> B)
symb tany ty.                                    % any
symb functional, relational : functionality.     % func / pred
symb arg argmode -> ty -> arg.                   % symb in, out : argmode.

pred data-type   o:string, o:int, o:srcloc.                      % data tm.
pred constructor o:string, o:any, o:ty, o:srcloc.                % symb app tm -> tm -> tm.
pred signature   o:string, o:any, o:functionality, o:list arg, o:bool, o:srcloc.
pred type-abbrev o:ty, o:ty, o:srcloc.
pred clause      o:any, o:int, o:srcloc, o:list attribute, o:(pred), o:(pred).
pred premises    o:srcloc, o:list span.                              % the places of the goals of a body
pred closed-clause o:int, o:any.                                    % with -closed
pred chr-rule    o:int, o:srcloc, o:list attribute, o:list any,
                 o:list sequent, o:list sequent, o:option (pred), o:option sequent.
```

For example, for

```elpi
data tm.
symb lam (tm -> tm) -> tm.
func rev list A -> list A.
rev L R :- std.rev L R.
```

`elpi-reflect` prints

```elpi
reflect.data-type "tm" 0 (reflect.srcloc "f.elpi" 1 0).
reflect.constructor "lam" lam (reflect.tarrow (reflect.tarrow (reflect.tcon "tm" []) (reflect.tcon "tm" [])) (reflect.tcon "tm" [])) (reflect.srcloc "f.elpi" 2 0).
reflect.signature "rev" rev reflect.functional [(reflect.arg reflect.in (reflect.tcon "list" [Ty_A])), (reflect.arg reflect.out (reflect.tcon "list" [Ty_A]))] ff (reflect.srcloc "f.elpi" 3 0).
reflect.clause rev 1 (reflect.srcloc "f.elpi" 4 0) [(reflect.binders [])] (rev L R) (std.rev L R).
reflect.premises (reflect.srcloc "f.elpi" 4 0) [(reflect.span "f.elpi" 4 11 4 22)].
```

### Conventions

- **Names** are fully qualified: Elpi's `namespace` and `shorten` are
  resolved the way the compiler does (a name used in `namespace foo { }`
  is `foo.name` when the block defines `foo.name`; with Elpi 4.1, when
  any block of `foo`, in the program or the builtins, defines it).  The second argument of
  `constructor` and `signature`, and the first of `clause`, is the constant
  itself (type `any`): it builds terms (`F = app, T = F X Y`) and it indexes
  the rules (`reflect.clause rev _ _ _ H B` only looks at the rules of
  `rev`).  The string is the same name, for printing.
- **Type parameters** are Elpi unification variables (`Ty_A` in the facts,
  `_Ty_A` when used once): every lookup of a fact gives fresh ones, so `reflect.constructor "::" _ T _, T = reflect.tarrow
  (reflect.tcon "int" []) _` instantiates `list A` at `list int`.
- **Rule variables** are the variables of the fact: each lookup of a
  `clause` fact gives a fresh copy of the rule, as `clause/2` does.  Bound
  variables (`pi x\`, `x\`) are Elpi lambdas; their source names are in the
  attribute `binders`.
- **Closed rules** (`-closed`): `closed-clause N F` gives each rule under
  N binders, one per variable (in order of appearance, each `_` a variable
  of its own): `F = V1\ .. VN\ clause P I Loc Attrs Head Body`.  Applied
  to N eigenvariables, `F` is the rule with no unification variable, which
  Elpi itself cannot do: no builtin finds the variables of a term, and a
  walk of the term in Elpi cannot take apart the application of a builtin
  written in OCaml (`var X`, `print X`, `X = Y` ...).  A tool can then
  compile the rule once into a closed clause of its own (elpi-debug,
  `../debug/lib/compiled.elpi`).  With a builtin giving the variables of a
  term (item 1 of [`../debug/ELPI-FEATURE-REQUESTS.md`](../debug/ELPI-FEATURE-REQUESTS.md)),
  the tool would close the rule itself and `-closed` would go.
- **Order**: the `Index` of a `clause` is its rank among the rules of its
  predicate in the order Elpi tries them, after `:before`, `:after`,
  `:replace` and `:remove`; the facts are printed in that order too.  Rules
  under `:if "VAR"` are kept only if `-D VAR` is given, as with `elpi`.
- **Spilling** `{f X}` is desugared as the compiler does it: a fresh
  variable `Spill_N` replaces it and the goal `f X Spill_N` runs just before
  the goal that contained it (before the whole body for a spill in the
  head).  `:autospill` is not desugared (the attribute `auto-spill` says so).
- **Premises**: `premises Loc Places` gives, for the rule whose `clause`
  fact has the location `Loc`, the place in the source of each goal of its
  body, in order: the goals of its top-level conjunction, nested
  conjunctions flattened as Elpi reads them (`a, (b, c)` has three
  goals), so that the N-th place is the N-th goal of the body as a tool
  sees it; none for a fact.  A place is `span File Line Column EndLine
  EndColumn`, its end the position just after the last character (lines
  from 1, columns from 0).  Elpi's parser keeps for each sub-term its
  start (line and column) and the offset of its end, not the line of the
  end: elpi-reflect reads the file again to find it (when it cannot, as
  for a path that Elpi's resolver gives but that does not exist, seen in
  dune's test sandbox, the end line is that of the last sub-term of the
  goal: wrong only when a line break follows its start, e.g. a closing
  parenthesis on a line of its own).  The goal of a
  spill `{f X}` (above) is placed at `f X`, inside the braces.
- **Head patterns** `uvar` and `P as X` become `reflect.uvar-pattern` and
  `reflect.as-pattern P X`: in a fact they would match, not be returned.
- **Body** of a fact is `true`; a body is a goal of type `(pred)` built
  with `,`, `;`, `pi`, `sigma`, `=>`, `==>`, `!`, … exactly as written.
- **CHR**: `chr-rule I Loc Attrs Clique ToMatch ToRemove Guard NewGoal` for
  `constraint Clique { rule ToMatch \ ToRemove | Guard <=> NewGoal. }`; a
  pattern `(E :> C ?- G)` is `reflect.sequent E C G`, a missing `E` or `C`
  is a fresh variable, a missing guard or new goal is `none`; `Loc` is
  the place of the first head of the rule (Elpi's own location of a rule
  starts at the end of the token before it, often on the line above).
- **Overloaded symbols** (declared twice with different types): the
  constant is cast to its type when that type is monomorphic
  (`((+) : int -> int -> int)`); for a polymorphic overloaded symbol such as
  `std.map` the constant is `_`.  The rules of an overloaded predicate are
  printed `:untyped`.
- **Connectives** (`:-`, `,`, `;`, `=>`, `==>`, `pi`, `sigma`, `uvar`,
  `as`) are syntax: their builtin declarations are not reflected.
- **Accumulated files** are reflected too (once each); the facts carry
  their own file in the locations.  Elpi's builtins and standard library
  (`std.*`) are not reflected: their rules are compiled into Elpi.

### Hints for a tool reading the rules (found while writing elpi-check)

- A conjunction `(A, B, C)` is one node with all its conjuncts (the parser
  flattens nested ones): the pattern `(X , Y)` matches only two conjuncts,
  so a pattern per length is needed (see `check/lib/goals.elpi`).
- The builtin `constant T Hd Args` takes apart an applied constant, but not
  a list (`[H | T]` is a node of its own) nor a connective or an FFI builtin
  (`,`, `=`, `pi`, `print` ...), which have no head.  With `T` unbound it
  builds `Hd` applied to `Args`; for a list, build `[H | T]` instead.
- In a rule head, `pi F` is not a pattern: write `(pi x\ F x)`.
- Many words are keywords of Elpi 4 and cannot name a predicate:
  `local`, `closed`, `prefix`, `before`, `name`, `mode`, `kind`, `type` ...

### Not supported (said plainly)

- a rule that uses a macro (`macro @m …`) is not reflected (a warning on
  stderr names it): the macro is not visible from the facts file;
- a spill under a lambda inside an atom (`std.map L (x\ y\ y = {f x})`) or
  in the hypothesis of an implication is left as written (warning);
- a spill `{f X}` is given one output (a function with two outputs is not
  spilled correctly);
- quotations (`{{ }}`) are printed back verbatim (only meaningful when the
  host declares a quotation, which standalone Elpi does not);
- `:autospill` rules are reflected without their spills.
