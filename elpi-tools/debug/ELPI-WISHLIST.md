# Three primitives elpi-debug would like from Elpi's core

elpi-debug (this directory) is a debugger for standalone Elpi 4 written as
a meta-interpreter in Elpi.  Everything it knows about the unification
variables of a run goes through the predicates of
[`lib/primitives.elpi`](lib/primitives.elpi).  Today they are stand-ins
written in Elpi; with builtins in Elpi's core only that file would change.
Below, each primitive: its contract, where elpi-debug uses it, what the
builtin would remove.  The declarations are written in Elpi 4's syntax, as in `builtin.elpi`
(where the data types of the real builtins would be `builtin data`).

## 1. `vars-of`: the variables of a term

```elpi
% [vars-of T Vs] Vs are the unification variables occurring in T, each
% once, in the order of their first occurrence (left to right, depth
% first), under binders and inside applications of builtins.  An applied
% variable (X a b) is given by its head X.  Binds nothing.
builtin func vars-of any -> list any.
```

**Used by** `primitives.elpi:trail-mark` (the variables in reach),
`ports.elpi:hyps-vars` (the variables of the hypothetical clauses in
scope), `lprolog.elpi:show-scope` (command `scope`),
`lprolog.elpi:mentions-var` (the occurs check in
`explain.elpi:flex-clash`), `machine.elpi:frame-json` (the variables of
each goal for the debug adapter).

**It removes** the walk of `lprolog.elpi:shape-of` for this purpose,
and its blind spots: the variables inside an application of a builtin
(`X is Y + 1` is one node that Elpi code cannot take apart) and inside a
conjunction of more than 16 goals (one pattern per arity).  Because of
the first, the debugger cannot close a rule of the program itself, and
elpi-reflect prints each rule a second time, closed
(`reflect.closed-clause N F`, its option `-closed`), for
`compiled.elpi:compile-rules`; with `vars-of`, the debugger would fetch a
rule under `pi x1..xn\` and bind its n variables to the x's, and that
detour would go.  It also removes a renaming: the walk gets the head of
an applied variable with the builtin `var`, which, on a variable kept in
Elpi's compact form (`G x`, printed `X0^1`), binds it to a new variable,
so the same variable shows under two numbers.

## 2. `uuid`: the identity of a variable

```elpi
% [uuid X N] N identifies the unification variable X for the whole run:
% different variables have different numbers, a variable keeps its number
% at every event and across backtracking.  Fails if X is not a variable;
% a variable bound to another one has the number of that one.
builtin func uuid any -> int.
```

elpi-debug names every variable `X<N>` (traces, explanations, the JSON of
`-machine`).  A printer option naming variables so would make
`lprolog.elpi:show-term` one call: the printer already has the line,
commented out, in `runtime.ml` (`"X" ^ string_of_int (uvar_id r)`).

**Used by** `primitives.elpi:uuid-name` and `term-string` (every printed
term, through `lprolog.elpi:show-term`), `primitives.elpi:trail-mark` and
`bound-since` (the stand-in of the trail), `machine.elpi:var-scope-json`
and `binding-json`.

**It removes** `primitives.elpi:printer-number` and `without-depths`: the
stand-in reads the number Elpi's printer gives a variable at its first
print (the only place where Elpi code sees a variable's identity), which
costs a print per name and is wrong inside a copy (`std.findall` prints
its copy with a table of its own, from `X0`).  A table kept in Elpi cannot
replace it: a safe refuses a term with variables, a local clause does not
outlive its goal, and `same_var` cannot tell a variable from one bound to
it.

## 3. The trail: `trail-mark` and `bindings-since`

(Enrico's suggestion.)

```elpi
data trail-mark.
% [trail-mark M] M marks the current point of the trail.
builtin func trail-mark -> trail-mark.

data pruning.
symb not-pruned pruning.
symb pruned-arguments int -> int -> int -> pruning.  % replaced by the variable of uuid U applied to K of its N arguments
symb pruned-scope list any -> pruning.               % replaced by a variable that may no longer depend on these eigenvariables

data binding.
symb binding int -> any -> pruning -> binding.       % uuid, value now, pruning

% [bindings-since M Bs] the bindings made since M and still in force: one
% per variable that existed at M and is bound now (the variables created
% after M are parts of the values), in the order of the trail.
builtin func bindings-since trail-mark -> list binding.
```

(`debug-unif T1 T2 Bs`, mark, `T1 = T2`, bindings since, is not needed by
elpi-debug: its head unification is split between Elpi's own clause
selection and the goals of `compiled.elpi`.)

**Used by** `ports.elpi:unify-port` (the unify event: mark, end of the
head unification, bindings since), `ports.elpi:call-port-marked` and
`exit-port-with-bindings` (new: mark at the call port, and the exit port
shows what the whole call computed), and through `made-bindings`,
`machine.elpi:bindings-json` (the debug adapter's Goal scope).

**It removes** the stand-in, a snapshot of the variables in reach
compared with what they are now (`primitives.elpi:var-snapshot`,
`bound-since`, `pruning-of`, which tests the scope of each variable by
trying to bind it to each eigenvariable in force), and
`ports.elpi:in-reach` / `hyps-vars`, which must tell the stand-in where
the variables a goal may bind are (its goal and the hypothetical clauses
in scope).  It would be exact (a variable reached only through the
constraint store is missed today) and its cost would be the bindings
made, not the size of the goal and of the hypotheses: every call could
take a mark, where today only the calls seen at their call port do.

## Not asked here, for retry

elpi-debug's retry (`r`) unwinds by failing: every event fails while the
request is pending, until the choice point placed before the call port.
Undoing the trail to a mark is not enough for it (the choice points
created since would remain).  It would need a mark that also records the
choice-point stack and a builtin that drops the choice points created
since and undoes the trail to the mark at once (a cut-and-fail to a given
point, as catch/throw).
