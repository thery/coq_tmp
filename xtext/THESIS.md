# From Coscoy's thesis to the code

Yann Coscoy, *Explication textuelle de preuves pour le calcul des
constructions inductives*, thesis, Université de Nice–Sophia Antipolis,
2000.  This table says, for each part of the thesis that xtext implements,
where it is in `elpi/` and which example reproduces its figure.  The names
in the code say what a predicate is for; the reference to the thesis is in
this file and in the comments.

Two translations exist, chosen by the switch `translation`
(`elpi/switches.elpi`; variable `XTEXT_TRANSLATION`):

- **staged** (default): the thesis's three stages, annotation,
  contraction, writing, each a predicate on its own data type
  (`staged.elpi`).  With the switch
  `selection` set to `thesis`, the second stage is the selection of
  chapter 4 (4.3.1) instead of the contraction.  The forms the
  thesis treats only in chapter 6 (eliminations, introductions, rewriting,
  `fix`) and `let`, `match`, casts are written by the direct writer, whose
  subproofs come back to the stages;
- **direct** (option): term to text in one walk (`transducer.elpi` and
  the files of its forms), with a contraction checked by tactics that is
  not the thesis's (below).

## Chapter 2: structural translation

| thesis | what | code |
|---|---|---|
| 2.1.5, Fig. 2.5–2.6 | minimal translation of the λ-calculus | `transducer.elpi` (`tr`), `abstractions.elpi`, `applications.elpi` |
| 2.2, Fig. 2.7–2.8 | specialised vocabulary (hypotheses, elements, propositions) | `kinds.elpi` (`binder-kind`), the words in `../lexicon/` |
| 2.3.1–2.3.2 | functions of several variables, the flexible syntax (contracted λ and applications) | stage 2, `contract` in `staged.elpi` |
| 2.3.3, Fig. 2.10 | the four rules for an application, the first that applies | `application-text` in `staged.elpi` (one clause per rule) |
| 2.3.3, Fig. 2.11 | Tauto, maximal contraction: "En appliquant l'hypothèse h3 à h1 et h2 nous avons C" | `examples-staged-maximal/Tauto.md` |
| 2.3.3 (abstractions) | one sentence for a series of binders | `abstraction-series`, `binder-phrases` in `staged.elpi` |

## Chapter 3: type expressions

| thesis | what | code |
|---|---|---|
| 3.1.2 | the double annotation ((M : Tc) : Tr) | the type `annot` (`single`, `double`) in `staged.elpi` |
| 3.2.4, Fig. 3.3 | weak head normal form | `whnf` in `printing.elpi` |
| 3.3.1, Fig. 3.4 | synthesis of types (Var, Const, Abs, App) | `synth` in `type-expressions.elpi` |
| 3.3.2 | inheritance of types, from the statement | `required`, `req` in `type-expressions.elpi`; the statement in `document.elpi` (`top-run`) |
| 3.3.4, Fig. 3.9 | the double computation Γ; Tr ⊢ M ↪ ((M:Tc):Tr), rules Var, Const, App1, App2, Abs | stage 1, `annotate` in `staged.elpi` (one clause per rule) |
| 3.3.4, Fig. 3.10 | Trans_Inv, doubly annotated, not contracted (L1–L5) | `examples-staged-none/Trans_Inv.md` |
| 3.4.1 | a conclusion says Tc, then "that is" Tr when they differ | `conclusion-parts` in `staged.elpi` |
| 3.4.2, Fig. 3.11 | guarded contraction: redundant double annotation, weak and strong contraction of the abstraction, contraction of the application | stage 2 in `staged.elpi`: `redundant-annotation`, `contract-body`, `variable-parts` (strong), `merge-application`, `merges`; the statement stops at the first abstraction whose annotation is double (`statement-stops-at`, `single-annotation`) |
| 3.4.2, Fig. 3.12 | Trans_Inv, maximal contraction | `examples-staged-maximal/Trans_Inv.md` |
| 3.4.2, Fig. 3.13 | Trans_Inv, guarded contraction | `examples/Trans_Inv.md` |

The direct writer also has a contraction of application steps
(`applications.elpi`, `contract-premises`, strategies `none`, `guarded`,
`maximal`), guarded by tactics rather than by the annotations: it is not
the contraction of Fig. 3.11.

## Chapter 4: the selection of type annotations, the subproofs

| thesis | what | code |
|---|---|---|
| 4.3.1, Fig. 4.10 | selection of the type expressions the text keeps, five rewriting rules; switch `selection` = `thesis` (variable `XTEXT_SELECTION`), stage 2 in place of the contraction | `select` in `staged.elpi` |
| 4.3.1, rules 1-3 (redundant type expressions, successive abstractions, successive applications) | the guarded contraction of Fig. 3.11: the same three rules | `select` calls `contract "guarded"` |
| 4.3.1, rules 4-5 (argument, head of application) | an identifier loses its single annotation as argument or head of an application | `identifiers-unannotated`, `application-argument`, `application-head` in `staged.elpi` |
| 4.3.1, Fig. 4.11 | one term per rule, before and after | `selection.v` (`rule_redundant`, `rule_abstractions`, `rule_applications`, `rule_argument`, `rule_head`) |
| 4.4.1, Fig. 4.23-4.24 | ABCD with all its annotations, then with its selected annotations | `selection.v` (`check-selection "ABCD"`; the term is printed by `aterm-string`); its text `examples-staged-selection/ABCD.md` |
| 4.4.1, Fig. 4.30 ("Nous appliquons h2 à h4 et P1") | an argument with no annotation is named in the sentence of its application | rules (2) and (4) of `application-text` in `staged.elpi` (`named-only`, `texts-and-names`) |
| 4.3.2, Fig. 4.12 | translatable occurrences: the head of a type annotation, the body of an abstraction, the function of an application, and an argument whose function has the type T ⇒ T' (T a proposition, T' not depending on it); a proof argument that is not translatable is written as a term; switch `naming` = `all` or `shared` (variable `XTEXT_NAMING`), after the selection | `translatable` in `subproofs.elpi` (`arg-kind` in `kinds.elpi` for T ⇒ T') |
| 4.3.2, Fig. 4.13 | argument of an abstraction: a binder of a proposition is a hypothesis only when the rest of the type does not depend on it, else a variable ("Let b : B") | `abstraction-binder-kind` in `kinds.elpi`, used by the statement (`top-run`, `document.elpi`) and the series of abstractions (`series-binder-kind`, `staged.elpi`) |
| 4.3.3, Fig. 4.14 | β-expansion: each translatable subproof that is the function or an argument of an application and keeps a type expression becomes a local definition, let P : T = M, in postfix order; Dewey names under a named abstraction (rules Cast, App♡♡, App♡◇, App◇♡, App◇◇, Abs, Ident, Défaut) | `name-subproofs`, `name-in-scope`, `name-node`, `name-part`, `name-subproof` in `subproofs.elpi`; the types `alet`, `aresult`, `named` in `staged.elpi` |
| 4.3.3, Fig. 4.16, 4.27 | ABCD with its intermediate results, let P1 : C = (h3 h4) in let P2 : B = (h2 h4 P1) in let P3 : C = (h3 h4) in ((h1 h4 P2 P3) : D) | `subproofs.v` (`check-naming "ABCD" "all"`), exactly |
| 4.3.3, Fig. 4.17 | suppression of doublets: a subproof whose type a result in scope proves is not proved again (P3 is P1); switch `naming` = `shared` | first clause of `name-subproof`; `subproofs.v` (`check-naming "ABCD" "shared"`), exactly |
| 4.4.1, Fig. 4.30 ("Preuve P1 : montrons C. Nous appliquons h3 à h4. Fin de P1. ...") | the text of a named result: a step whose claim is followed by its name, used by name afterwards | `write (alet ...)` and `conclusion-parts (named ...)` in `staged.elpi`; `subproofs.v` (`check-text "ABCD"`, in French and English), `examples-staged-naming/ABCD.md`, `examples-staged-shared/ABCD.md` |

Where the code departs from the thesis:

- Fig. 4.23 writes the applications with all their arguments and leaves
  out the types of the partial applications (`h1 h4 : B -> C -> D`); the
  annotation of `selection.v` has them.  The selected term is Fig. 4.24
  exactly.
- The thesis annotates only proofs; the arguments that are not proofs
  (App2, the `z`, `y`, `x` of Trans_Inv) carry their type, written "The
  element z belongs to E", and the rule "argument of application" leaves
  it out when the argument is an identifier.
- Fig. 2.10 has no rule for an application whose arguments are partly
  identifiers with no annotation: rules (2) and (4) name them after "to"
  ("Applying h2 to h4, we have B") or "with" ("By application, with z, y
  and x, we have ..."), as Fig. 4.30 does ("Nous appliquons h2 à h4 et
  P1"); without the switch `naming`, the arguments that keep a text are
  written above, unnamed; with it, they are the named results of 4.3.3.
- A term argument is named as formulas print it (`BinInt.Z.le`, not
  `le`), so that two constants with the same short name differ.
- 4.3.2-4.3.3 run only after the selection (switch `naming` with
  `selection` = `thesis`; another selection is an error), as in the
  thesis, where they come after it.  They are one switch, `naming`, not
  values of `selection`: they are further steps with their own variant
  (doublets suppressed or not), and the thesis keeps P3 in Fig. 4.27 but
  removes it in Fig. 4.17, so both are values (`all`, `shared`).
- Fig. 4.12 marks occurrences; here the stage keeps the proofs that are
  translatable as they are and turns the others into terms (`aelem`,
  written "The element g b belongs to A").  `subproofs.v` prints the marks
  M♡ (not on abstractions, whose bodies are always translatable).
- Fig. 4.14 is written for an application of one argument.  The term
  here has applications of several arguments (after the selection,
  Fig. 4.24): the function, then the arguments from left to right, each
  by the rule of Fig. 4.14 that fits it; this gives Fig. 4.27's order
  (P1 inside P2, then P3), which the binary rules alone do not (App◇♡ does
  not look into its function).
- Rule Abs numbers the results under an abstraction under the index
  of the abstraction (P_{i.1}), for every abstraction.  Here only a named
  abstraction does (its results are P2.1, P2.2, ...); the abstractions of
  the proof itself, and those joined in one series, continue the
  numbering of their scope.  Fig. 4.27 needs this: by Abs taken
  literally, the results of ABCD, under eight abstractions, would be
  P1.1.1.1.1.1.1.1.1, not P1, P2, P3.
- The forms of chapter 6 (eliminations, `match`, ...) are written by the
  direct writer, and their subproofs come back to the stages later.  Their
  results are numbered like those of an abstraction, under the next index
  (P1.1 in a case of an argument), or continue the scope when the form is
  the whole proof of the scope.  Each case is its own scope (two cases
  may both have a P1.1).  With `shared`, a result of an enclosing scope
  can serve inside a case.
- Doublets (Fig. 4.17) are found among the named results in scope, by
  their types (as the thesis says: the proofs are not compared), not
  among the hypotheses.
- The text of a named result (Fig. 4.30, "Preuve P1 : montrons C. Nous
  appliquons h3 à h4. Fin de P1.") is one step whose claim is followed by
  the name, "Applying h3 to h4, we have `C` (P1)" ("En appliquant h3 à
  h4, nous avons `C` (P1)"), the way a text names a hypothesis: the
  format of the texts (cyp's) has no "Proof P1 ... End of P1" block.  A
  named result proved by several lines has them below its claim, as any
  subproof.  The definitions come before the step that uses them; when
  that step is itself a subproof written below its claim, they are below
  it too.

## Chapter 5: tactics, scripts and implicit information

| thesis | what | code |
|---|---|---|
| 5.2.2 (Cast') | "that is" for a conversion | `that-is` (`expected-types.elpi`) |
| 5.4 (pragmatic method) | a subproof built by a tactic, written as one step "by T" | `tactic-step` in `transducer.elpi` |
| 5.4 (extended App) | arguments that can be inferred are left out | `apply-rest`, `inferable` in `applications.elpi` |
| 5.4, applied to formulas | formulas that type-check again (the implicit arguments printed when needed) | `reparse.elpi` |

## Chapter 6: inductive constructions

| thesis | what | code |
|---|---|---|
| 6.2.1 (Constr) | introduction theorems | `tr-intro` in `inductive-text.elpi`, `intro-info` in `inductive.elpi` |
| 6.2.2 (Elim*) | elimination theorems, first and second kind | `tr-elim1`, `tr-elim2` in `inductive-text.elpi` |
| 6.3.1, 6.3.2 | eliminations with one case, with zero cases | `inductive-text.elpi` |
| 6.3.3, 6.3.4 | dependent eliminations, eliminations with recursion (base and inductive cases) | `inductive-text.elpi` (`recursive`) |
| 6.4.1 | implicit arguments in eliminations: the generalised predicate (the motive) of a dependent elimination left out when it follows from the instance and the object, "Montrons (P x0) par une preuve par cas sur x0"; the motive is found as Rocq's elim finds it, the indices and the object abstracted in the instance, and must be the motive of the proof; always on, as 5.4's inferable arguments (`XTEXT_OFF=motive` for measurements) | `instance-without-motive`, `abstract-terms` in `applications.elpi`; `implicit_motive.v` (the schemes of 6.3.3-6.3.4: booleans, pairs, lists; `add_0_r'`; a motive not found, `partial_motive`) |
| 6.4.2 | elimination theorems recognised by their type, whatever their name | `elim-info` in `inductive.elpi` |
| (end of 6.4.2) | rewriting: the thesis asks for a specific rule but gives none | `tr-rewrite` in `inductive-text.elpi`; the rewriting principles recognised by their type, `rewrite-info` in `inductive.elpi` |

Where 6.4.1 is followed or not:

- 6.4.1 has no figure; its examples are the schemes of 6.3.3 and 6.3.4
  ("Pour montrer (P b0), par une preuve par cas, généralisons en
  λb:bool.(P b) avant de le spécialiser à b0", the pairs, the lists by
  induction), reproduced in `implicit_motive.v` with the light text
  6.4.1 gives, "Montrons (P x0) par une preuve par cas sur x0" (here
  "Montrons `P b0` par analyse de cas sur `b0` (bool, bool_ind):", the
  words of the lexicon, and the cases kept; the closing step proves the
  instance, so there is no "In particular").  An elimination with one
  case has no announcement (6.3.3): its line becomes "Par définition de
  prod (prod_ind) sur `p0`, montrons `P p0`:".
- 6.4.1 says that finding the predicate is higher-order unification,
  undecidable, and asks for an external unification.  The one used is
  Rocq's for elim: abstract the object (and the indices) in the
  instance; the predicate is left out when this gives the motive of the
  proof, which is the generate-and-test of 5.4 with this unification.
  All 20 English texts of `examples/` that generalised before now leave
  the motive out (with `half_le`, an elimination with one case: 21).
- A limit of cyp, the reader of the texts: its step *by C_ind* is
  Rocq's eapply, which does not find the motive as elim does (on
  n <= n + m it finds le n).  In 14 English texts, cyp no longer proves
  the closing step of the elimination (README, "Checking the texts with
  cyp"); the texts are still read.  The change cyp needs, a separate
  task: for a claim announced "by induction on x0" (or "by case analysis
  on x0"), abstract x0 in the goal before applying the theorem (elim x0
  using C_ind).  That is the first step 6.4.1 asks for, the evaluation
  extended so that ElimOpen can be evaluated without the predicate.

## Not implemented

- Chapter 4, the reversible translation: a script language whose concrete
  syntax is natural language, so that a text can be read back into a proof.
  Of chapter 4, the selection of type annotations (4.3.1), the
  characterisation of subproofs (4.3.2) and the naming of intermediate
  results (4.3.3) are implemented, as stages of the translation; not the
  script language (4.2, 4.3.4: Fig. 4.18-4.21, 4.28-4.29), so a text
  cannot be read back into a term.  Fig. 4.15 (a β-expansion that keeps
  the tree, P1.1 inside P1) is not produced: the thesis shows it to
  motivate the postfix one, Fig. 4.16, which is the algorithm.

## From L. Théry's thesis (1994)

| thesis | what | code |
|---|---|---|
| 3.3.3 | a proof in progress: each open goal written "Prove G" | `open-goal` in `transducer.elpi`, `explain-partial` in `document.elpi` |
