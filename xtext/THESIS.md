# From Coscoy's thesis to the code

Yann Coscoy, *Explication textuelle de preuves pour le calcul des
constructions inductives*, thesis, Université de Nice–Sophia Antipolis,
2000.  This table says, for each part of the thesis that xtext implements,
where it is in `elpi/` and which example reproduces its figure.  The names
in the code say what a predicate is for; the reference to the thesis is in
this file and in the comments.

Two translations exist, chosen by the switch `xtext-translation`
(`Explain.v`; variable `XTEXT_TRANSLATION`):

- **direct** (default): term to text in one walk (`transducer.elpi` and
  the files of its forms);
- **staged**: the thesis's three stages, annotation, contraction, writing,
  each a predicate on its own data type (`staged.elpi`).  The forms the
  thesis treats only in chapter 6 (eliminations, introductions, rewriting,
  `fix`) and `let`, `match`, casts are written by the direct writer, whose
  subproofs come back to the stages.

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
| 3.1.2 | the double annotation ((M : Tc) : Tr) | the type `annot` (`one`, `two`) in `staged.elpi` |
| 3.2.4, Fig. 3.3 | weak head normal form | `whnf` in `annotation.elpi` |
| 3.3.1, Fig. 3.4 | synthesis of types (Var, Const, Abs, App) | `synth` in `annotation.elpi` |
| 3.3.2 | inheritance of types, from the statement | `required`, `req`; the statement in `document.elpi` (`top-run`) |
| 3.3.4, Fig. 3.9 | the double computation Γ; Tr ⊢ M ↪ ((M:Tc):Tr), rules Var, Const, App1, App2, Abs | stage 1, `annotate` in `staged.elpi` (one clause per rule); in one pass: `d-annot`, `d-abs` in `annotation.elpi` |
| 3.3.4, Fig. 3.10 | Trans_Inv, doubly annotated, not contracted (L1–L5) | `examples-double/Trans_Inv.md` |
| 3.4.1 | a conclusion says Tc, then "that is" Tr when they differ | `conclusion-parts` in `staged.elpi`; `add-equiv`, `equiv-text` in `annotation.elpi` |
| 3.4.2, Fig. 3.11 | guarded contraction: redundant double annotation, weak and strong contraction of the abstraction, contraction of the application | stage 2 in `staged.elpi`: `redundant-annotation`, `contract-body`, `variable-parts` (strong), `merge-application`, `merges` |
| 3.4.2, Fig. 3.12 | Trans_Inv, maximal contraction | `examples-staged-maximal/Trans_Inv.md` |
| 3.4.2, Fig. 3.13 | Trans_Inv, guarded contraction | `examples-staged-guarded/Trans_Inv.md` |

The direct writer also has a contraction of application steps
(`applications.elpi`, `contract`, strategies `none`, `guarded`,
`maximal`), guarded by tactics rather than by the annotations: it is not
the contraction of Fig. 3.11.

## Chapter 5: tactics, scripts and implicit information

| thesis | what | code |
|---|---|---|
| 5.2.2 (Cast') | "that is" for a conversion | `that-is` (`document.elpi`) |
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
| (end of 6.4.2) | rewriting: the thesis asks for a specific rule but gives none | `tr-rewrite` in `inductive-text.elpi` (by the name of the theorem: to be generalised) |

## Not implemented

- Chapter 4, the reversible translation: a script language whose concrete
  syntax is natural language, so that a text can be read back into a proof.
- 4.3.1, the selection of type annotations: which formulas a text can leave
  out.
- 6.4.1, leaving out implicit arguments in eliminations.

## From L. Théry's thesis (1994)

| thesis | what | code |
|---|---|---|
| 3.3.3 | a proof in progress: each open goal written "Prove G" | `open-goal` in `transducer.elpi`, `explain-partial` in `document.elpi` |
