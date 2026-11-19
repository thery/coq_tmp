# xtext: proofs as text

`ExtractText foo.` prints the proof of the constant `foo` as text.  It follows
the *basic transducer* of *Extracting Text from Proofs* (Y. Coscoy,
G. Kahn, L. Théry, TLCA 1995, section 3.1), extended to inductive types
after chapter 6 of Y. Coscoy's thesis *Explication textuelle de preuves
pour le calcul des constructions inductives* (Nice, 2000).  The text is
coarse but faithful: one list item per step, every formula of the proof in
Rocq syntax, and the rule or lemma used by each step.  It is meant to be
rewritten into fluent prose later (by hand or by an LLM).  Written to a
file, it is in the Markdown format of [cyp](../cyp/README.md), so that cyp
can check it again.

```coq
From XText Require Import ExtractText.
ExtractText foo.                                (* prints the text, as plain text *)
ExtractText foo in "fr".                        (* in French; also it de nl ru zh ar ko la *)
#[tags] ExtractText foo.                        (* prints it in the format of proof texts *)
ExtractText foo to "examples/foo.md".           (* writes it to a file, in that format *)
ExtractText foo to "examples/fr/foo.md" in "fr".   (* the same in French *)
ExtractText foo to "foo.typ".                   (* in Typst, for a PDF: ../prooftext/pdf.sh foo.typ *)
```

The two forms of a text.  The text that `ExtractText foo.` prints (in
Rocq's messages, the goals panel) is for a reader, close to Coscoy's
output: plain text, the formulas in Rocq syntax without backticks, the
justifications without markup, no header and no title; the list of the
steps stays:

```
Let n : nat. We prove n + 0 = n.

- We prove n + 0 = n by induction on n (nat, nat_ind):
  - Case 1 (base): we prove 0 = 0.
    - By definition of eq (eq_refl), we have 0 = 0.
```

A file (`to "foo.md"`), and the text printed with the attribute
`#[tags]` (`#[tags] ExtractText foo in "fr".` in French), are in the
format of proof texts, with its header, its title and its classes
(`` `n : nat`{.var} ``, `*eq_refl*{.just}`): the form that cyp, the Typst
writer and the gallery read.  Both are written by the same writer
(`prooftext.write-document-as`, the markup being a parameter);
`printed.v` tests them, in the ten languages.  `ExtractText_partial`
prints in the same way.

Proofs ending with `Qed` work too: the body is read with
`coq.env.const-body`, which rocq-elpi gives even for opaque
constants.

## Build

Rocq 9.1.1, Elpi 4.0.0 and rocq-elpi master (opam switch `elpi5`, the
switch of cyp).  xtext needs two libraries that it shares with cyp, and
nothing of cyp itself: the lexicon, `../lexicon` (logical name `Lexicon`,
the words of each language), and prooftext, `../prooftext` (logical name
`ProofText`, [the format of proof texts](../prooftext/README.md): the
document and its writer, the header, formulas with their roles, the
justifications `*X*{.just}`, fresh names, the tactics a text may name):

```sh
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5)"
make          # builds ExtractText.vo, then the example files, which write examples/*.md
```

## Files

`ExtractText.v` defines the commands `ExtractText` and `ExtractText_partial`, the
database `xtext.db` (the parameters: tactics, thresholds, switches, the
header's libraries) and loads the lexicon, prooftext and the writer.  The
writer is in `elpi/`, one file per subject, loaded in this order:

| file | what it does |
|---|---|
| `text-tree.elpi` | the data of a text: lines with sub-lines (and a closing paragraph), the text of a proof (its lines and its conclusion), kinds of binders and of arguments, the \* context |
| `printing.elpi` | terms: the names of the context, the terms sent to Rocq (`away-from-context`, `whnf`), printing (`pp`, bound names renamed, fresh names of binders), formulas with their roles (`formula`), beta-reduction |
| `switches.elpi` | the switches (`switch`, see "Switches"), and `XTEXT_OFF` |
| `words.elpi` | sentences: a sentence is a list of parts (phrases of the lexicon, text, formulas, enumerations "A, B and C"), `sentence` writes it in the language of the text |
| `reparse.elpi` | formulas that type-check again (the implicit arguments to print); the type of a term (`typ`); the name of a justification (`justification-of`, `short-name`) |
| `kinds.elpi` | the kind of a binder (`Let`, `Assume`, arbitrary element) and of an argument (specialisation, modus ponens); with the switch `naming`, a binder the rest of the type depends on is a variable (thesis Fig. 4.13) |
| `inductive.elpi` | introduction, elimination and rewriting theorems, recognised by their type |
| `declarations.elpi` | the predicates that a file uses and a later one defines |
| `transducer.elpi` | the text of a proof term, by its form; open goals; subproofs closed by a tactic |
| `expected-types.elpi` | the type expected at the place of a subproof, and "that is" |
| `abstractions.elpi` | series of abstractions, local definitions |
| `applications.elpi` | specialisations and modus ponens, inferable arguments, the contraction of application steps |
| `inductive-text.elpi` | the text of introductions, eliminations (cases), `match`, `fix`, rewriting |
| `conclusions.elpi` | every node has its conclusion: a line that only introduces variables or hypotheses merged with its only sub-line, or given a closing paragraph (the tree of the 2003 paper) |
| `document.elpi` | the statement, the document and its header (written by prooftext), the check of the vocabulary |
| `type-expressions.elpi` | type expressions after chapter 3 of the thesis: synthesis, equality, the type required of the proof |
| `staged.elpi` | the translation in three stages of the thesis, and the selection of type annotations (see ["The staged translation"](doc/staged-translation.md)) |
| `subproofs.elpi` | after the selection, the subproofs of the thesis (4.3.2, 4.3.3): which proofs the text translates, and a name P1, P2, ... for each intermediate result (switch `naming`, see ["The subproofs"](doc/subproofs.md)) |

[THESIS.md](THESIS.md) maps each rule and figure of Coscoy's thesis to the
predicate that implements it, and to the example that reproduces it.

Examples and checks:

- `paper.v` (the paper's examples), `lemmas.v` (small lemmas),
  `inductive.v` (induction, case analysis, rewriting, fix), `thesis.v`
  (the theses' examples), `stdlib.v` (lemmas of Rocq's Stdlib),
  `elim_type.v` (elimination principles recognised by their type),
  `implicit_motive.v` (the motive of an elimination left out, thesis
  6.4.1),
  `partial.v` (proofs in progress), `reals.v` (two texts on real
  numbers, with fractions, powers, square roots and absolute values, for
  the formulas in mathematics of their PDF): the texts in `examples/` (87
  with those of a private case study, kept in a private branch, 82 here);
- `multilingual.v`: 12 of them in each of the other languages of the
  lexicon (`examples/fr`, `it`, `de`, `nl`, `ru`, `zh`, `ar`, `ko`, `la`);
- `typst_examples.v`: ten texts in Typst, for their PDFs (`examples-typst/`,
  five in English, one each in French, Arabic, Chinese, Russian and Korean;
  see "The PDF of a text");
- `vocab_check.v`: the vocabulary of each language, and the tactic names
  that xtext writes (they must be prooftext's);
- `printed.v`: the two forms of a text, plain (printed) and tagged
  (`#[tags]`, the files), in the ten languages;
- `selection.v`: the selection of type annotations (thesis 4.3.1) on
  ABCD (Fig. 4.24), Trans_Inv and one term per rule (Fig. 4.11): each
  selected term is checked against the expected one;
- `subproofs.v`: the subproofs (thesis 4.3.2-4.3.3) on ABCD (Fig. 4.27,
  Fig. 4.17, the text of Fig. 4.30 in French and English) and on terms
  with a dependent argument, a named abstraction and a case analysis
  inside an application;
- `implicit_motive.v`: the motive of a dependent elimination left out
  (thesis 6.4.1) on the schemes of 6.3.3-6.3.4 (booleans, pairs, lists,
  `examples/bool_P.md`, `prod_P.md`, `list_P.md`), on `add_0_r'`, and
  kept where it is not found again (`partial_motive`): each text is
  checked against the expected one;
- `test-helpers.elpi`: what these three test files share (`expect`, the
  text of a theorem from its statement on, `expect-text`);
- `examples-staged-none/`, `examples-staged-maximal/`,
  `examples-staged-selection/` (with `XTEXT_SELECTION=thesis`),
  `examples-staged-naming/` and `examples-staged-shared/` (with
  `XTEXT_SELECTION=thesis` and `XTEXT_NAMING=all` or `shared`),
  `examples-direct/` (with `XTEXT_TRANSLATION=direct`): the texts with
  other switches, written by `sh make_variant.sh NAME VAR=VALUE...` (e.g.
  `sh make_variant.sh direct XTEXT_TRANSLATION=direct`);
- `measure.sh`, `measure_all.sh`: times and sizes of the texts;
- optional checks with cyp: `cyprun.sh`, `cyp-check/` (cyp's results,
  see ["Checking the texts with cyp"](doc/checking-with-cyp.md)), `cyp-check/roles_check.sh`.

## Switches

Five switches change how a text is written (`elpi/switches.elpi`).  Each
has an environment variable that sets it and a default, in `xtext.db`
(`xtext-switch Name Variable Default`, `ExtractText.v`):

| switch | variable | values | default |
|---|---|---|---|
| `translation` | `XTEXT_TRANSLATION` | `staged` (the three stages of the thesis, see ["The staged translation"](doc/staged-translation.md)), `direct` (one walk; its contraction is checked by tactics, not the thesis's) | `staged` |
| `contraction` | `XTEXT_CONTRACTION` | `none`, `guarded`, `maximal` (thesis 3.4.2, see ["Contraction of application steps"](doc/contraction-eliminations-partial.md#2-contraction-of-application-steps-thesis-342-fig-311-313)) | `guarded` |
| `selection` | `XTEXT_SELECTION` | `none` (the contraction decides), `thesis` (the selection of thesis 4.3.1, in place of the contraction; staged translation only, see ["The selection of type annotations"](doc/staged-translation.md#the-selection-of-type-annotations-thesis-431-fig-410)) | `none` |
| `naming` | `XTEXT_NAMING` | `none`, `all` (after the selection, each subproof used in an application is named, P1, P2, ..., and proved before the step that uses it; thesis 4.3.2-4.3.3), `shared` (the same, a result proved once for each type in scope); needs `selection` = `thesis` (see ["The subproofs"](doc/subproofs.md)) | `none` |
| `lang` | `XTEXT_LANG` | the languages of the lexicon: `en`, `fr`, `it`, `de`, `nl`, `ru`, `zh`, `ar`, `ko`, `la` | `en` |

The language given to the command (`ExtractText foo in "fr"`) comes before
the variable.  A value that is not in the list, an empty one included,
is an error, so that a misspelt value does not silently give the texts of
another setting.  The switches are read when `ExtractText` runs, from the
environment of the Rocq process that runs it: `make` does not see the
variables, so after changing one, compile the example files again
(`make_variant.sh` does it in a copy of the directory).  `XTEXT_OFF`
(see ["Inferable arguments, tactics, unfolding"](doc/generic-mechanisms.md)) switches mechanisms off for measurements; an unknown name in it
is an error too.

## The output

```markdown
---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (h). We prove `B \/ A`{.claim}.

- We prove `B \/ A` by case analysis on *h*{.just} (or, *or_ind*{.just}):
  - Case 1: we prove `A -> B \/ A`{.claim}.
    - Assume `A`{.hyp} (i). By definition of or (*or_intror*{.just}), from *i*{.just} we deduce `B \/ A`{.claim}.
  - Case 2: we prove `B -> B \/ A`{.claim}.
    - Assume `B`{.hyp} (j). By definition of or (*or_introl*{.just}), from *j*{.just} we deduce `B \/ A`{.claim}.

  We have `B \/ A`{.claim} in all cases.
```

- the text is in the format of proof texts ([prooftext](../prooftext/README.md)),
  the tree of the 2003 paper (*Colouring proofs*, UITP 2003), which cyp
  reads: a list item is a node, with one conclusion, its variables and
  hypotheses scope over its sub-items, and only what is tagged is used;
- the header: `require` loads the libraries (`xtext-header-require` in
  `xtext.db`) and the file that defines the theorem; a text in another
  language has `lang: fr`, `lang: ko`, ...; `by` lists the tactics that
  check a guarded contraction (`xtext-guard-tactic`), which cyp then tries
  on the steps that name none;
- the abstractions at the top of the proof make the statement (`Let`,
  `Assume`, `We prove`), the top node;
- each formula that cyp uses carries its role (`{.var}`, `{.hyp}`,
  `{.claim}`, `{.fact}`); a fact is a hypothesis or a conclusion in scope
  (the conclusion of an earlier step that the sentence repeats: "Rewriting
  with `m + 0 = m`{.fact}"); the other formulas are untagged, shown and not
  used: a goal announced before its cases, the object of an induction, a
  witness, the first form of "A, that is B" (the second, the one the steps
  after it use, is the conclusion);
- **every node has its conclusion** (`elpi/conclusions.elpi`): a line that
  only introduces variables or hypotheses (`Let`, `Assume`) is merged with
  its only sub-item ("Assume `A`{.hyp} (i). By definition ..."), or its
  last sub-item becomes its closing paragraph, after the other sub-items
  (the forward style of the paper), or, when that sub-item has sub-items
  of its own, a closing paragraph says its conclusion again ("We have
  `C`{.claim}."); an elimination with several cases is one node, the goal
  announced, the cases, and the conclusion in its closing paragraph ("We
  have ... in all cases");
- **justifications**: the names that justify a step are emphasised and
  tagged where the sentence names them, `*X*{.just}`: hypotheses ("By
  *h4*{.just} we have", "Applying *i*{.just} to *k*{.just}"), lemmas,
  constructors ("By definition of or (*or_intror*{.just})"), elimination
  theorems ("(nat, *nat_ind*{.just})"), intermediate results
  (*P1*{.just}), and the tactic of a tactic-built step ("By
  *lia*{.just} we have", see ["Tactic-built subproofs"](doc/generic-mechanisms.md#5-tactic-built-subproofs-thesis-54-the-pragmatic-method));
  a node may have several.  cyp applies them (`*X*{.just}`: cyp runs no
  tactic code).  The name of a lemma is as short as Rocq finds it, but
  keeps the name of its library unless the text imports that library (the
  prelude, the file of the theorem): `Classical_Prop.classic`,
  `PeanoNat.Nat.add_comm`, since cyp reads the text with its `require`
  line only.  A term that is no proof (`Applying f to A and P`), a `match`
  and a first-kind elimination on a type with indices (`le_ind`: its
  motive is not found from the goal by unification) are not
  justifications; cyp's default tactics close those steps when they can;
- the lines "The element `t` belongs to `T`" (the terms an application
  is given) are untagged remarks, and are left out when `t` is a variable,
  whose type the text gave where it introduced it;
- a subproof is a list item: its conclusion, with the lines that lead to
  it indented below.

### The PDF of a text

`ExtractText foo to "foo.typ".` writes the text in Typst instead of Markdown
(the same document, written by prooftext's `write-typst`), and
`../prooftext/pdf.sh foo.typ` makes `foo.pdf`.  `../prooftext/pdf.sh
examples/foo.md` does both steps from a Markdown text.  The PDF shows each
role of a formula in its own style (and a legend), the steps indented as
in the list, and the header as a small title block; the names (h) link to
the steps that introduced them, the lemmas of the corelib and the stdlib
to their documentation; a text in Arabic is laid out from right
to left.  The formulas are mathematics (∀ n ∈ ℕ, n + 0 = n), printed from
their Rocq terms by prooftext's table of notations (`pdf.sh --code` keeps
the Rocq code; `pdf.sh --html` makes an HTML page); `reals.v` sets the
`require` line of its texts (the parameter `xtext-header-require`) so that
the reader finds the notations of the reals.  The same template shows the texts that cyp has checked, with
their statuses (`../prooftext/pdf.sh cyp-check/foo.checked.md`).  The
design, the fonts and the tests are in
[prooftext](../prooftext/README.md#the-pdf-of-a-proof-text-typst).

### The words: the lexicon

xtext takes every phrase it writes from the lexicon
([`../lexicon`](../lexicon/README.md), `lang_<lang>.elpi`), a library of
its own that cyp reads proofs with too; xtext does not depend on cyp.
Next to the reading table (`phrase Lang Phrase Role`), each table has the
writer's phrases:

- `write-role Lang Use Phrase Role`: a phrase that gives the role of the
  formula after it (`"deduce" "we deduce" rclaim`, `"rewriting"
  "rewriting with" rfact`).  It is also a phrase of the reading table (one
  clause, `phrase L P R :- write-role L _ P R`), so cyp reads it with the
  role the writer means;
- `write-word Lang Use Words`: the other words (`"by-cases" "by case
  analysis"`, `"base" "base"`).

A sentence is written as a list of parts, `wd Use` (the phrase of a use in
the language of the text) and `tx S` (formulas, names, punctuation), joined
by spaces (`text-of-parts` in `elpi/words.elpi`); a sentence that starts with a phrase
has its first letter capitalised, by the capital letters of the lexicon
(`sentence`).  The same lists serve every language: only the table changes,
so a text in another language has the structure, the formulas and the
justifications of the English one (`Supposons ... (h). Montrons ...`).
The language is the switch `lang` (see "Switches").  A phrase that the
lexicon puts after its formula (`phrase-after`, Korean) is moved after the
parts it governs: up to the next phrase of a role, the next `,` `.` `:`
`;` outside parentheses, or the justification (`` `A`{.hyp} (h) 그리고
`B`{.hyp} (h2) 라고 가정하자 ``).  Otherwise the word order is the English
one: the tables avoid the phrases that would need another order
(`Considérons un élément arbitraire x : A`), and the Korean texts keep the
English order of the words that give no role (`` `B \/ A`{.claim} 모든
경우에 이다 ``, "in all cases ... is").  No text was reviewed by a speaker.

- `vocab_check.v` checks that each language has a phrase for every use
  of the English table and that the phrases of roles are in lower case.
- `cyp-check/roles_check.sh` (optional, with cyp) read every text with
  cyp's reader twice, with the tags and without them, and listed the
  formulas whose role came only from the tag.  It no longer runs: cyp
  reads only the tags now (no word gives a role), so the question is
  gone.  The last figures, before the tree: over the 82 English texts (1933 lines), 94 lines: the goal
  announced before a proof by cases (``We prove `G`{.fact} by case
  analysis on ...``, a mention after a claim phrase, 65 lines) and the
  object in ``Going back to the definition of and (match) in `A /\ B`{.fact}``
  (29 lines; `in` is too common a word to be a fact phrase for cyp).
  Over the 12 texts (136 lines) of each other language: fr 11, it 11,
  de 12, nl 11, ru 11, zh 12, ar 11, ko 8, la 10 lines.

## More

- [The rules of the paper and of the thesis](doc/rules.md), and the departures from them.
- [Examples and tests](doc/examples.md): the example files, the examples of the two theses compared with their texts, and the larger examples of Stdlib.
- [Inferable arguments, tactics, unfolding](doc/generic-mechanisms.md): formulas that type-check again, inferable arguments, tactic-built subproofs, "that is", local definitions, and their measurements.
- [Contraction, eliminations by their type, proofs in progress](doc/contraction-eliminations-partial.md), and their measurements.
- [Checking the texts with cyp](doc/checking-with-cyp.md): cyp's results on the texts.
- [The staged translation](doc/staged-translation.md) of the thesis, and the selection of type annotations.
- [The subproofs](doc/subproofs.md) of the thesis: the translatable occurrences and the named intermediate results.
- [THESIS.md](THESIS.md): each rule and figure of Coscoy's thesis, with the predicate and the example.

## Not done

- The section "Further optimizations" of the paper (one-use
  assumptions, `Trivially`, `A fortiori`, dependence analysis).
- The specific wordings of the paper's figures for the usual connectives
  and classical reasoning (`Altogether`, `Obviously`, `If we have ...
  Otherwise`).
- From the thesis: the scripts of its chapter 4 (4.2, 4.3.4: a text that
  can be read back into a proof term); the selection of type annotations
  and the subproofs (4.3.1-4.3.3) are done.
- Mutual fixpoints (`mfix`) and `cofix` are left unchanged, as are
  non-propositional subterms.
- The `require` line of the header is the same for every text (the
  parameter `xtext-header-require`, and the file of the theorem): it does
  not list what a proof uses; the load path for cyp is added by
  `cyprun.sh`.
