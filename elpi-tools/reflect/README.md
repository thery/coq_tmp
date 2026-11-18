# elpi-reflect: an Elpi program as Elpi data

Elpi has no builtin that returns the rules of the running program (Prolog's
`clause/2`).  `elpi-reflect` fills the gap from outside: an OCaml program
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

    elpi-reflect [-I DIR].. [-D VAR].. [-builtins] FILE..     # facts on standard output

With `-builtins` it also prints the declarations (data types, constructors,
signatures; not the rules) of Elpi's builtins and standard library, e.g.
the signature of `std.rev`.

Standalone Elpi 4 only (opam switch `elpi5`), not Rocq-Elpi.

## The format

All names live in the namespace `reflect`.  Excerpt of
[`reflect.elpi`](reflect.elpi):

```elpi
symb srcloc string -> int -> int -> srcloc.      % file, line (from 1), column (from 0)

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
pred chr-rule    o:int, o:srcloc, o:list attribute, o:list any,
                 o:list sequent, o:list sequent, o:option (pred), o:option sequent.
```

For example, for

```elpi
data tm.
symb lam (tm -> tm) -> tm.
func rev list A -> list A.
rev L R :- rev.aux L [] R.
```

`elpi-reflect` prints

```elpi
reflect.data-type "tm" 0 (reflect.srcloc "f.elpi" 1 0).
reflect.constructor "lam" lam (reflect.tarrow (reflect.tarrow (reflect.tcon "tm" []) (reflect.tcon "tm" [])) (reflect.tcon "tm" [])) (reflect.srcloc "f.elpi" 2 0).
reflect.signature "rev" rev reflect.functional [reflect.arg reflect.in (reflect.tcon "list" [A]), reflect.arg reflect.out (reflect.tcon "list" [A])] ff (reflect.srcloc "f.elpi" 3 0).
reflect.clause rev 1 (reflect.srcloc "f.elpi" 4 0) [reflect.binders []] (rev L R) (rev.aux L [] R).
```

### Conventions

- **Names** are fully qualified: Elpi's `namespace` and `shorten` are
  resolved the way the compiler does (a name used in `namespace foo { }`
  is `foo.name` when the block defines `foo.name`).  The second argument of
  `constructor` and `signature`, and the first of `clause`, is the constant
  itself (type `any`): it builds terms (`F = app, T = F X Y`) and it indexes
  the rules (`reflect.clause rev _ _ _ H B` only looks at the rules of
  `rev`).  The string is the same name, for printing.
- **Type parameters** are Elpi unification variables: every lookup of a
  fact gives fresh ones, so `reflect.constructor "::" _ T _, T = reflect.tarrow
  (reflect.tcon "int" []) _` instantiates `list A` at `list int`.
- **Rule variables** are the variables of the fact: each lookup of a
  `clause` fact gives a fresh copy of the rule, as `clause/2` does.  Bound
  variables (`pi x\`, `x\`) are Elpi lambdas; their source names are in the
  attribute `binders`.
- **Order**: the `Index` of a `clause` is its rank among the rules of its
  predicate in the order Elpi tries them, after `:before`, `:after`,
  `:replace` and `:remove`; the facts are printed in that order too.  Rules
  under `:if "VAR"` are kept only if `-D VAR` is given, as with `elpi`.
- **Spilling** `{f X}` is desugared as the compiler does it: a fresh
  variable `Spill_N` replaces it and the goal `f X Spill_N` runs just before
  the goal that contained it (before the whole body for a spill in the
  head).  `:autospill` is not desugared (the attribute `auto-spill` says so).
- **Head patterns** `uvar` and `P as X` become `reflect.uvar-pattern` and
  `reflect.as-pattern P X`: in a fact they would match, not be returned.
- **Body** of a fact is `true`; a body is a goal of type `(pred)` built
  with `,`, `;`, `pi`, `sigma`, `=>`, `==>`, `!`, … exactly as written.
- **CHR**: `chr-rule I Loc Attrs Clique ToMatch ToRemove Guard NewGoal` for
  `constraint Clique { rule ToMatch \ ToRemove | Guard <=> NewGoal. }`; a
  pattern `(E :> C ?- G)` is `reflect.sequent E C G`, a missing `E` or `C`
  is a fresh variable, a missing guard or new goal is `none`.
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

### Not supported (said plainly)

- macros (`macro @m …`) are printed unexpanded, so a reflected rule that
  uses one does not type check: the tool stops with an error naming it;
- quotations (`{{ }}`) are printed back verbatim (only meaningful when the
  host declares a quotation, which standalone Elpi does not);
- `:autospill` rules are reflected without their spills.
