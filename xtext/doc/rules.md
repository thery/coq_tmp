[Back to the README of xtext](../README.md)

# The rules of the paper and of the thesis

The rules by which xtext writes each form of proof term, and where it departs from the paper and the thesis.

## Rules of the paper (TLCA 1995, section 3.1)

- **Rules for abstraction**, in their **iterated** form (a run of
  binders of the same kind gives one line):
  - `λl:A_Type. M` → `Let l : A` ... `We have proved τ`;
  - `λh:A_Prop. M` → `Assume A (h) and ...` ... `We have proved τ`;
  - `λx:A_Set. M` → `Let us consider an arbitrary x : A` ... `We have τ, since x is arbitrary`
    (several: `Let us choose arbitrarily ...` ... `Thus we have τ`).
- **Rules for application**, in their **iterated** form (arguments are
  cut into maximal runs of the same kind):
  - specialisation `M_{∀x:P.Q} N` → `M` then `In particular τ`;
  - modus ponens `M_{P⇒Q} N1..Nk` → `- N1 ... - Nk - M` then `We deduce τ`.
- **Rules for identifiers**: `h_τ` → `By h we have τ`; theorem `T_τ` →
  `Using T we get τ`.
- The **\* context** is used at the top of the proof, where the theorem
  is announced (the statement), and inside the cases (see below).
- Expressions that match no rule are **left unchanged**: `Using t we get τ`.

## Rules of the thesis (chapter 6, inductive constructions)

They replace the paper's rules for introduction and elimination theorems.

- **Constr** (6.2.1): a constructor is a definition step, not a theorem:
  `By definition of C (K), we have τ`.  When all its premises are
  hypotheses, it reads `By definition of C (K), from A (h) we deduce τ`
  (the thesis's `Par définition, de H0 nous déduisons B ∨ A`).  Otherwise
  the premises come first, as dashed subproofs.
- **ElimOpen / ElimCase / ElimClose** (6.2.2): an elimination
  `C_ind ... H` is read as a proof by cases, announced first, with the
  object eliminated: `We prove τ by case analysis on A ∨ B (h) (or,
  or_ind):`, then `Case 1: ...`, ..., then `We have τ in all cases`.
  Cases are numbered in Dewey notation (`Case 1.2:`).
- **One case** (6.3.1, `and`, `ex`): there is no case, only a return to
  the definition: `Going back to the definition of and (and_ind) in x ∧ y
  (h), we prove τ:` with the branch below it, and no closing sentence.
- **Zero cases** (6.3.2, `False`): `By contradiction (False, ...), from
  False (f) we can deduce τ`.
- **Dependent eliminations** (6.3.3, `bool`, `nat`): the goal is
  generalised before it is specialised: `To prove n + 0 = n by induction
  (nat, nat_ind), we generalise it to forall n0, n0 + 0 = n0:`, the cases,
  `These cases being exhaustive, we deduce ...`, then `In particular n + 0 = n`.
- **Eliminations with recursion** (6.3.4): a binder of a branch whose
  type mentions the motive is an induction hypothesis (`Assume by
  induction hypothesis m + 0 = m (IH)`).  The cases are marked `(base)` or
  `(inductive)`, and the proof is announced `by induction` instead of `by
  case analysis`.  All of this is read from the type of the elimination
  theorem, so it works for `nat_ind`, `list_ind`, `le_ind`, ...
- **Implicit arguments in eliminations** (6.4.1): the generalised
  statement (the motive) of a dependent elimination is left out when it
  can be found again from the instance proved and the object eliminated:
  `We prove n + 0 = n by induction on n (nat, nat_ind):`, the cases,
  `These cases being exhaustive, we deduce n + 0 = n`, with no
  generalisation and no `In particular` (the thesis's "Montrons (P x0)
  par une preuve par cas sur x0").  The motive is found as Rocq's `elim`
  (and `pattern`) find it: the indices and the object are abstracted in
  the instance, and the result must be the motive of the proof
  (`instance-without-motive`, `abstract-terms` in `applications.elpi`).
  A motive that abstracts only some occurrences of the object is not
  found, and the text generalises first, as above (`partial_motive` in
  `implicit_motive.v`).  It is always on, as the inferable arguments of
  5.4; `XTEXT_OFF=motive` switches it off.  It shortens every dependent
  elimination of `examples/`: 50 generated texts change (21 in English,
  27 in the other languages, 2 in Typst), and 21 in each variant.  cyp
  reads and proves them: its justification *nat_ind*{.just} applies an elimination
  principle as `elim` does, the goal abstracted over the variable first
  (`eapply nat_ind` alone unifies `?P ?x` with `le n (n + m)`
  first-order and gives `le n`).

## Departures from the paper and the thesis

- The shorter rule `We have h` for assumptions and the variants for
  applications to variables (`Using f with f1, f2 ...`) are not used: they
  drop formulas, and the text must keep all of them.
- The constructor and the elimination theorem are named (`(or_intror)`,
  `(nat_ind)`), which the thesis leaves out, so that the reader, or cyp,
  can check the step.
- A witness of a constructor is shown: `By definition of ex (ex_intro)
  with witness t` (the paper's `The element c proves τ`), since it is part
  of the proof.
- Each case states its goal (`Case 1: we prove τ1`), and its branch is
  read in the \* context (no `We have proved τ1` at its end), since the
  goal is already stated at the head of the case.
- The generalised predicate of a dependent elimination is written as a
  statement (`forall n0, ...`), not as a λ-term: it reads better and
  type-checks as a formula.
- `match` is read as an elimination (the thesis hides the primitive
  operator behind `C_ind`): first kind if the inductive type is in `Prop`,
  else second kind.  Elimination theorems are found by the shape of
  their type (6.4.2, see ["Elimination principles recognised by their type"](contraction-eliminations-partial.md#6-elimination-principles-recognised-by-their-type-thesis-642)), not by their name.
- **Rewriting** (`eq_ind`, `eq_ind_r`, `eq_rect`, ...): the thesis says
  (end of 6.4.2) that the generic text is poor and that a specific rule is
  needed, but gives none.  Here the proof of `P x` and the proof of the
  equation come first, as dashed subproofs, then `Rewriting with y = x
  from right to left (eq_ind_r), we get P y`.  A rewriting principle is
  recognised by its type, `forall A (x : A) (P : A -> _), P x -> forall y,
  x = y -> P y` (or `y = x`, from right to left), where `=` is an
  equality type (an inductive proposition with parameters `A`, `x : A` and
  one constructor of type `x = x`), whatever its name.
- **`fix`** (not treated by the thesis; 6.3.4 studies only the types of
  elimination theorems): `We prove τ by recursion on n (fix f):` with the
  body below it.  A recursive call reads `By induction hypothesis (the
  recursive call f) we have τ`, and a `match` whose case calls `f` is an
  inductive case.  Nothing checks that the calls are on smaller
  arguments, since Rocq already did.
- An elimination with several cases is one node of the tree: the goal
  announced (untagged), the cases below it, and the conclusion in its
  closing paragraph (`These cases being exhaustive, we deduce ...`).  It
  is justified by the elimination theorem, named where the text names it
  (`(nat, *nat_ind*{.just})`), which cyp applies to the cases; a `match`,
  and a first-kind elimination on a type with indices (`le_ind`), have no
  justification (see ["The output"](../README.md#the-output)).
- Intro patterns leave redexes `fun h => (fun i => M) h`; they are reduced
  and the user's name `i` is kept.  Other redexes are cuts and are
  rendered with the application rules.  Casts are skipped; `let x := N in
  M` is read as `(fun x => M) N`.
- A product `A -> Q` whose domain is not a proposition is read as a
  specialisation, not as a function application.
- Formulas are printed by Rocq, with notations.  A bound name that clashes
  with the context is renamed (`n0`), and anonymous hypotheses are called
  `h`.  An equality with a bare constructor on one side gets its type,
  `([]) = ([]) :> list A`, since `[] = []` does not type-check again.
- Markdown lists replace the paper's dashes; a subproof's lines come
  below its conclusion (indented), not above it.
- `Let us consider` / `Let us choose` instead of `Consider` / `Choose`, so
  that the line reads as a binder for cyp.
