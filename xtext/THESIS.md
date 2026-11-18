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

## Chapter 4: the selection of type annotations

| thesis | what | code |
|---|---|---|
| 4.3.1, Fig. 4.10 | selection of the type expressions the text keeps, five rewriting rules; switch `selection` = `thesis` (variable `XTEXT_SELECTION`), stage 2 in place of the contraction | `select` in `staged.elpi` |
| 4.3.1, rules 1-3 (redundant type expressions, successive abstractions, successive applications) | the guarded contraction of Fig. 3.11: the same three rules | `select` calls `contract "guarded"` |
| 4.3.1, rules 4-5 (argument, head of application) | an identifier loses its single annotation as argument or head of an application | `identifiers-unannotated`, `application-argument`, `application-head` in `staged.elpi` |
| 4.3.1, Fig. 4.11 | one term per rule, before and after | `selection.v` (`rule_redundant`, `rule_abstractions`, `rule_applications`, `rule_argument`, `rule_head`) |
| 4.4.1, Fig. 4.23-4.24 | ABCD with all its annotations, then with its selected annotations | `selection.v` (`check-selection "ABCD"`; the term is printed by `aterm-string`); its text `examples-staged-selection/ABCD.md` |
| 4.4.1, Fig. 4.30 ("Nous appliquons h2 à h4 et P1") | an argument with no annotation is named in the sentence of its application | rules (2) and (4) of `application-text` in `staged.elpi` (`named-only`, `texts-and-names`) |

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
  P1"); the arguments that keep a text are written above, unnamed (the
  names P1, P2, P3 come from 4.3.3, not implemented).
- A term argument is named as formulas print it (`BinInt.Z.le`, not
  `le`), so that two constants with the same short name differ.

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
| 6.4.2 | elimination theorems recognised by their type, whatever their name | `elim-info` in `inductive.elpi` |
| (end of 6.4.2) | rewriting: the thesis asks for a specific rule but gives none | `tr-rewrite` in `inductive-text.elpi`; the rewriting principles recognised by their type, `rewrite-info` in `inductive.elpi` |

## Not implemented

- Chapter 4, the reversible translation: a script language whose concrete
  syntax is natural language, so that a text can be read back into a proof.
  Of chapter 4, only the selection of type annotations (4.3.1) is
  implemented: not the characterisation of subproofs (4.3.2) nor the
  naming of intermediate results by η-expansion (4.3.3, the P1, P2, P3
  of Fig. 4.27-4.30).
- 6.4.1, leaving out implicit arguments in eliminations.

## From L. Théry's thesis (1994)

| thesis | what | code |
|---|---|---|
| 3.3.3 | a proof in progress: each open goal written "Prove G" | `open-goal` in `transducer.elpi`, `explain-partial` in `document.elpi` |
