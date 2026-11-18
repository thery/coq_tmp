# xtext: proofs as text

`Explain foo.` prints the proof of the constant `foo` as text.  It follows
the *basic transducer* of *Extracting Text from Proofs* (Y. Coscoy,
G. Kahn, L. Théry, TLCA 1995, section 3.1), extended to inductive types
after chapter 6 of Y. Coscoy's thesis *Explication textuelle de preuves
pour le calcul des constructions inductives* (Nice, 2000).  The text is
coarse but faithful: one list item per step, every formula of the proof in
backticks in Rocq syntax, and the rule or lemma used by each step.  It is
meant to be rewritten into fluent prose later (by hand or by an LLM), and
it is written in the Markdown format of [cyp](../cyp/README.md), so that
cyp can check it again.

```coq
From XText Require Import Explain.
Explain foo.                                (* prints the text *)
Explain foo to "examples/foo.md".           (* writes it to a file *)
Explain foo to "examples/fr/foo.md" in "fr".   (* in French; also it de nl ru zh ar ko la *)
```

Proofs ending with `Qed` work too: the body is read with
`coq.env.const-body`, which rocq-elpi gives even for opaque
constants.

## Build

Rocq 9.1.1, Elpi 4.0.0 and rocq-elpi 3.5.1 (opam switch `elpi4`, the
switch of cyp).  xtext needs two libraries that it shares with cyp, and
nothing of cyp itself: the lexicon, `../lexicon` (logical name `Lexicon`,
the words of each language), and prooftext, `../prooftext` (logical name
`ProofText`, [the format of proof texts](../prooftext/README.md): the
document and its writer, the header, formulas with their roles, the
justification `*by X*`, fresh names, the tactics a text may name):

```sh
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi4)"
make          # builds Explain.vo, then the example files, which write examples/*.md
```

[THESIS.md](THESIS.md) maps each rule and figure of Coscoy's thesis to the
predicate that implements it, and to the example that reproduces it.

Files: `Explain.v` (the command) and the writer in `elpi/`, one file per
subject, loaded in this order:

- `text-tree.elpi` (lines and the text of a proof), `printing.elpi`
  (terms and formulas), `switches.elpi` (the switches, below), `words.elpi` (words and sentences from the
  lexicon), `reparse.elpi` (formulas that type-check again), `kinds.elpi`
  (kinds of binders and arguments), `inductive.elpi` (recognising
  introduction and elimination theorems), `declarations.elpi` (predicates
  used by a file before the one that defines them);
- `transducer.elpi` (the text of a proof term, by its form),
  `abstractions.elpi`, `applications.elpi` (with the contraction of their
  steps), `inductive-text.elpi` (introductions, eliminations, fix,
  rewriting), `document.elpi` (the statement, the header, the document);
- `type-expressions.elpi` (synthesis and equality of type expressions,
  chapter 3 of the thesis), `sentences.elpi` and `staged.elpi` (the
  translation in three stages, below).

Examples: 
`paper.v` (the paper's examples), `lemmas.v` (small lemmas),
`inductive.v` (induction, case analysis, rewriting, fix), `thesis.v`,
`stdlib.v`, `elim_type.v`, `partial.v` (see below): the texts in
`examples/` (82 with those of a private case study, kept in a private
branch); `multilingual.v`: 12 of them in each of the other
languages of the lexicon (`examples/fr`, `it`, `de`, `nl`, `ru`, `zh`, `ar`,
`ko`, `la`); `vocab_check.v` (the vocabulary, below); the optional checks with cyp:
`cyprun.sh`, `cyp-check/` (cyp's results, below), and
`cyp-check/roles_check.sh`; `examples-staged-none/`, `examples-staged-maximal/`,
`examples-staged-guarded/`: the texts with other switches, written by
`sh make_variant.sh NAME VAR=VALUE...` (e.g. `sh make_variant.sh
staged-guarded XTEXT_TRANSLATION=staged XTEXT_CONTRACTION=guarded`).

## Switches

Three switches change how a text is written (`elpi/switches.elpi`).  Each
has an environment variable that sets it and a default, in `xtext.db`
(`xtext-switch Name Variable Default`, `Explain.v`):

| switch | variable | values | default |
|---|---|---|---|
| `translation` | `XTEXT_TRANSLATION` | `direct` (one walk), `staged` (the three stages of the thesis, below) | `direct` |
| `contraction` | `XTEXT_CONTRACTION` | `none`, `guarded`, `maximal` (thesis 3.4.2, below) | `guarded` |
| `lang` | `XTEXT_LANG` | the languages of the lexicon: `en`, `fr`, `it`, `de`, `nl`, `ru`, `zh`, `ar`, `ko`, `la` | `en` |

The language given to the command (`Explain foo in "fr"`) comes before
the variable.  A value that is not in the list, an empty one included,
is an error, so that a misspelt value does not silently give the texts of
another setting.  The switches are read when `Explain` runs, from the
environment of the Rocq process that runs it: `make` does not see the
variables, so after changing one, compile the example files again
(`make_variant.sh` does it in a copy of the directory).  `XTEXT_OFF`
(below) switches mechanisms off for measurements; an unknown name in it
is an error too.

## The output

```markdown
---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (h). We prove `B \/ A`{.claim}.

- We prove `B \/ A`{.fact} by case analysis on `A \/ B`{.fact} (h) (or, or_ind):
- Case 1: we prove `A -> B \/ A`{.claim}.
  - Assume `A`{.hyp} (i).
    - By definition of or (or_intror), from `A`{.fact} (i) we deduce `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- Case 2: we prove `B -> B \/ A`{.claim}.
  ...
- We have `B \/ A`{.claim} in all cases.
```

- the header is cyp's; `require` loads the file that defines the theorem;
  a text in another language has `lang: fr`, `lang: ko`, ...;
- the abstractions at the top of the proof make the statement (`Let`,
  `Assume`, `We prove`);
- each formula carries its cyp role (`{.var}`, `{.hyp}`, `{.claim}`,
  `{.fact}`), so that cyp does not have to guess it from the words;
- a subproof is a list item: its conclusion, with the lines that lead to
  it indented below;
- each step names its rule or lemma, and its justification for cyp is a
  name, which cyp applies (`*by X*`: cyp runs no tactic code): a theorem
  step and a constructor step carry the full name of the theorem or of the
  constructor, `*by Stdlib.Lists.List.rev_unit*`; the closing step of a
  dependent elimination (the generalised statement) the elimination
  theorem, `*by Corelib.Init.Datatypes.nat_ind*`; a step proved by a
  tactic (below) the tactic's name, `*by lia*`.  The closing steps of a
  `match` and of a first-kind elimination (`or_ind`, `le_ind`) have none:
  the motive is not found from the goal by unification when the type has
  indices, and a `match` would need `destruct`; cyp's default tactics
  close them when they can.

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
- `cyp-check/roles_check.sh` (optional, with cyp) reads every text with
  cyp's reader twice, with the tags
  and without them, and lists the formulas whose role comes only from
  the tag.  Over the 82 English texts (1933 lines), 94 lines: the goal
  announced before a proof by cases (``We prove `G`{.fact} by case
  analysis on ...``, a mention after a claim phrase, 65 lines) and the
  object in ``Going back to the definition of and (match) in `A /\ B`{.fact}``
  (29 lines; `in` is too common a word to be a fact phrase for cyp).
  Over the 12 texts (136 lines) of each other language: fr 11, it 11,
  de 12, nl 11, ru 11, zh 12, ar 11, ko 8, la 10 lines.

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
  their type (6.4.2, see below), not by their name.
- **Rewriting** (`eq_ind`, `eq_ind_r`, `eq_rect`, ...): the thesis says
  (end of 6.4.2) that the generic text is poor and that a specific rule is
  needed, but gives none.  Here the proof of `P x` and the proof of the
  equation come first, as dashed subproofs, then `Rewriting with y = x
  from right to left (eq_ind_r), we get P y`.
- **`fix`** (not treated by the thesis; 6.3.4 studies only the types of
  elimination theorems): `We prove τ by recursion on n (fix f):` with the
  body below it.  A recursive call reads `By induction hypothesis (the
  recursive call f) we have τ`, and a `match` whose case calls `f` is an
  inductive case.  Nothing checks that the calls are on smaller
  arguments, since Rocq already did.
- The closing step of a dependent elimination (`These cases being
  exhaustive, we deduce ...`) is justified by the elimination theorem
  (`*by Corelib.Init.Datatypes.nat_ind*`), which cyp applies to the case
  claims; the closing step of a first-kind elimination or of a `match`
  (`We have τ in all cases`) has no justification (see "The output").
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

## Tests

- `paper.v`: the examples of the paper: the identity, the proof (S),
  `∨intro`, commutativity of `∨` by `or_ind`, `∀m, 0 ≤ m` by `nat_ind`,
  and the three examples of the last figure (praeclarum, a symmetric and
  transitive relation is nearly reflexive, the drinker's principle).
- `lemmas.v`: `and_swap`, `or_swap`, `imp_trans`, `not_not_intro`,
  `ex_forall`, `forall_and`, `add_0_r'`, `le_add_r'`, `double_neg_em`.
- `inductive.v`: induction on `nat` with rewriting (`plus_n_Sm'`), on
  lists (`app_nil_r'`), rewriting only (`eq_trans'`), induction on a
  hypothesis `n <= m` (`le_n_S'`), a `Fixpoint` on `nat` (`le_0_n'`) and
  on lists (`length_app'`), case analysis on a boolean (`bool_cases`).

All these texts are generated in `examples/`; cyp's results are below
("Checking the texts with cyp").
## The examples of the two theses (`thesis.v`)

The proof terms are written as close as possible to the λ-terms of the
theses.

**Tauto** (Coscoy, Fig. 1.5, 2.6, 2.8, 2.11): `fun A B C h1 h2 h3 => h3 h1 h2`.
- Same: the statement (`Let A B C`, `Assume A (h1) and B (h2) and A -> B -> C (h3)`).
- Different: the thesis writes one step, `En appliquant l'hypothèse h3 à
  h1 et h2 nous avons C` (its application-to-variables rule).  xtext
  writes the three hypotheses as dashed lines, then `We deduce C`, so
  that every formula is shown.  The thesis's closing `Nous avons montré
  ∀A, B, C ...` is the statement here.

**Trans_Inv** (Coscoy, Fig. 3.5-3.13 and the final form, Fig. 5.11):
`fun E R h x y z h1 h2 => h z y x h2 h1`, with `Rel`, `Trans`, `Inv` as
in the thesis.
- Same: the binders (`Let E : Set`, `Let R : Rel E`, `Assume Trans E R
  (h)`, `Let x y z : E`, `Assume Inv E R x y (h1) and Inv E R y z (h2)`),
  the two hypotheses used, then the application of `h`.
- With "that is" (mechanism (4) below) and the inferable arguments (3b),
  the text is now that of Fig. 3.13: `By h2 we have Inv E R y z, that is R
  z y`, `By h1 we have Inv E R x y, that is R y x`, `By h we have Trans E
  R, that is forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`, `We
  deduce R z x, that is Inv E R x z`, and the statement is the declared
  one, `We prove Inv E R x z`.  The step `In particular R z y -> R y x
  -> R z x` is gone: `z`, `y`, `x` are inferred (as in Fig. 5.11, `En
  appliquant h à h2 et h1`).
- Still different from Fig. 5.11: the goal `Trans E (Inv E R)` is not
  announced with its unfolding before the binders `x y z` (`Montrons
  (Trans E (Inv E R)), ce qui est équivalent à ∀x, y, z ...`): the
  statement is `Let x y z : E`, `Assume ...`, as the λ-term gives it.
  With the staged translation, the statement is `We prove Trans E (Inv E
  R)`, the binders are a step, and its conclusion says the unfolding
  (`that is Trans E (Inv E R)`): see "The staged translation" below.

**ABCD** (Coscoy, Fig. 4.28, 5.5, 5.6):
`fun A B C D h1 h2 h3 h4 => h1 h4 (h2 h4 (h3 h4)) (h3 h4)`.
- Same: the same three intermediate results, in the same order
  (`C`, then `B` from `h2`, then `C` again, then `D`).
- Different: the thesis names them (`P1`, `P2`, `P3`) and writes one line
  each (`En appliquant h3 à h4, nous avons C (P1)`); xtext nests them as
  dashed subproofs with the hypotheses shown.  The thesis's Fig. 5.6 has a
  typo (`D (h4)` for `A (h4)`).

**or_com** (Coscoy, Fig. 6.2, 6.3, 6.5):
`fun A B H => or_ind (fun H0 => or_intror H0) (fun H0 => or_introl H0) H`.
- Same as Fig. 6.5 (ElimOpen / ElimCase / ElimClose): `We prove B \/ A by
  case analysis on A \/ B (H)`, two cases with `Assume A (H0)` and `By
  definition of or ..., from A (H0) we deduce B \/ A`, then `We have B \/ A
  in all cases`.
- Different: the names of the rules are given, and each case states its
  goal (`Case 1: we prove A -> B \/ A`).

**or_sym_nd** (Théry, Fig. 3.3): `a \/ b -> b \/ a` with a `match`.
The thesis's text: `Supposons a ∨ b (1) / a ∨ b par (1) / Il y a donc deux
cas / Si a (2) / a par (2) / donc b ∨ a évidemment / Si b (3) ... / nous
avons b ∨ a dans les deux cas / nous avons prouvé a ∨ b ⊃ b ∨ a`.  xtext
gives the same steps in the same order, except the first `a ∨ b par (1)`,
which is in the case-analysis line (`on a \/ b (H1)`), and the
hypothesis of the implication, which is in the statement.

**praeclarum_nd** (Théry, section 3.3.3):
`conj (proj1 H1 (proj1 H2)) (proj2 H1 (proj2 H2))`.  The thesis's final
text: `x par (2) / Nous en déduisons z par (1) / y par (2) / Nous en
déduisons t par (1) / Ceci réuni donne z ∧ t`.  Same structure (two
modus ponens, then the conjunction), but `proj1` and `proj2` are Rocq
theorems, not rules, so each ∧-elimination costs xtext two lines (`Using
proj1 we get ...`, `In particular ...`) where the thesis writes `par (1)`.

**ADD0** (Théry, section 4.9.2, HOL): `nat_ind (fun m => m + 0 = m)
eq_refl (fun m IH => f_equal S IH) m`.  An induction with a base case and
an inductive case, as in the thesis's HOL session.  Coscoy's rules
(6.3.3, 6.3.4) give the generalised statement, `(base)` and
`(inductive)`, and `Assume by induction hypothesis m0 + 0 = m0 (IH)`.

### xtext's wordings and Théry's Figures 3.4-3.6

| rule | Théry 1994 | xtext |
|---|---|---|
| ∧ intro | `ceci réuni donne A ∧ B` | `So by definition of and (conj), we have A /\ B` |
| ∨ intro | `donc, A ∨ B évidemment` | `By definition of or (or_introl), ... we have A \/ B` |
| ⊃ intro | `Supposons A (i)` ... `nous avons prouvé A ⊃ B` | `Assume A (i)` ... `We have proved A -> B` |
| ¬ intro | `Supposons A (j)` ... `d'où ¬A (en niant j)` | as ⊃ intro: `Assume A (j)` ... `We have proved A -> False` |
| ∀ intro | `Considérons un c arbitraire` ... `comme c était arbitraire, nous avons ∀x A` | `Let us consider an arbitrary c : T` ... `We have τ, since c is arbitrary` |
| ∃ intro | `par conséquent ∃x A` | `By definition of ex (ex_intro) with witness c, we have ...` |
| ∧ elim | `A ∧ B, donc C` | one case: `Going back to the definition of and ... in A /\ B (h)`; with `proj1`: `Using proj1`, `In particular` |
| ∨ elim | `Il y a donc deux cas: si A (k) ... si B (l) ... nous avons C dans les deux cas` | `We prove C by case analysis on A \/ B (h) ...: Case 1 ... Case 2 ... We have C in all cases` |
| ⊃ elim | `nous en déduisons B` | `We deduce B` |
| ¬ elim | `il y a une contradiction` | `We deduce False` |
| ∀ elim | `en particulier A[x\e]` | `In particular A[x\e]` |
| ∃ elim | `Dans ceci, choisissons c, tel que A[x\c] (m)` ... `(indépendamment de c)` | `Going back to the definition of ex ... Let us consider an arbitrary c ... Assume A (m)` |
| ⊥ elim | `(donc C)` | `By contradiction (False, ...), from False (f) we can deduce C` |
| closure | `A par (n)` | `By n we have A` |

The structure is the same as xtext's (the paper of 1995 descends from it):
a hypothesis opens an indented block, a rule with several premises lists
them, then states its conclusion.  The differences: xtext names the
constructors and theorems, has no special words for `¬` (a negation is
an implication to `False` in Rocq), and states the goal of each case.

The text of an **incomplete proof** (section 3.3.3), where each open goal
is written `Prouvez G` at its place, is now `Explain_partial` (below).

## More examples: theses, Stdlib

Files: `thesis.v` (the theses' examples, above), `stdlib.v` (40 lemmas
of Rocq's Stdlib, explained from the library itself: `Time Explain
app_assoc to ...`).  `measure.sh f.v` prints, for each text, the time of
`Explain` (Rocq's `Time`), the number of list items and the size;

What breaks or becomes unreadable on the large ones:

- **Generated proofs are explained as they are.**  `Nat.add_comm`,
  `Nat.mul_comm`, ... are proved with setoid rewriting: their texts (200-480
  items) are mostly about `Morphisms.Proper`, `ProperProxy`,
  `RelationClasses.Reflexive`, the internals of `rewrite`, not about
  arithmetic.  The certificates of `lia`, `ring` or `interval` appear as
  local definitions (`Let __ff be Tauto.IMPL (...)`) and lines of
  1500-2200 characters.  Now partly handled, see "Tactic-built
  subproofs" below.
- **Implicit arguments.**  Rocq prints `Equivalence eq` or `length [] =
  0` without the type, and these formulas do not type-check again: cyp
  marks them as errors, and all the steps after them too.  This is most of
  the "not proved" of the `Nat.*` and `length_*` texts.  Now handled,
  see "Formulas that type-check again" below.
- **Local definitions** (`Let hyp_list be nil`) had no form in cyp, so a
  later formula that used `hyp_list` was a Rocq error.  They are now
  written as cyp's local definitions (below).
- **Size**: `Nat.le_trans` (484 items) is generated in 0.5 s, but cyp
  does not finish it within its limit (300 s).

## Inferable arguments, tactics, unfolding

Four generic mechanisms, after Coscoy's thesis.  Each can be switched
off for measurements with the environment variable `XTEXT_OFF` (a
comma-separated list of `explicit`, `args`, `tactics`, `thatis`).

### (3a) Formulas that type-check again (thesis 5.4, applied to formulas)

Rocq's printer leaves out the implicit arguments, so `@eq (list A) []
[]` prints as `[] = []`, which does not type-check again.  For each
formula, xtext builds its *skeleton*: the implicit arguments of every
application become holes.  It elaborates the skeleton
(`coq.elaborate-skeleton`) and keeps the printed form only if the result
is ground and convertible to the formula.  Otherwise it decides
application by application, in the order of the term: the arguments of
an application are left out if the skeleton still elaborates back,
with the earlier applications as decided and the later ones written in
full.  The kept applications are printed `@f a1 .. an`, for example
`[] = (@nil A)` or `RelationClasses.Reflexive (@eq nat)`.

- Rocq's implicit status (`coq.arguments.implicit`) only says which
  arguments the printer can drop.  Re-elaboration decides which ones may
  stay dropped.
- Limits: a kept application under a binder cannot be put back into the
  printed text by the placeholder method used here, so the whole formula
  is printed with `Printing All` (`@eq nat (@length A ...)`).  A formula
  with more than 60 such applications is printed in full when the fast
  test fails.  The test is up to conversion and assumes that Rocq parses
  the printed text back to the skeleton (notations, scopes).
- Binder types (`Let`, `Assume`) and the local definitions get the same
  treatment.

### (3b) Inferable arguments of an application (thesis 5.4, the extended App)

A run of specialisations followed by a run of premises (`h z y x h2 h1`)
is written as one modus ponens step when the specialised arguments can be
inferred.  The test: the application with these arguments as holes
elaborates, against its type, back to the same term.  The step `In
particular R z y -> R y x -> R z x` then disappears.  Nothing is
dropped by name.

### (5) Tactic-built subproofs (thesis 5.4, the pragmatic method)

A proper subproof whose proof term has at least `xtext-threshold` nodes
(default 300) is first tried with the tactics of `xtext-tactic`, in
order, on its statement in its own context.  The defaults are
`tauto` then `lia`, each with a 2 s time limit.  The first tactic that
closes it gives one step, `We have P *by lia*`, instead of the walk
through the term.  The success of the tactic is the guarantee; no
constant is recognised by its name.

- Where: on every subproof but the whole proof (the body of the theorem,
  and the body of a cast or `let` that is the whole proof).  The size is
  that of the proof term, so the large terms built by `lia`, `ring` or
  setoid rewriting are the ones tried.  Short subproofs keep their text.
- Parameters, in the Elpi database `xtext.db` (`Explain.v`):
  `xtext-tactic Ltac Text` (an Ltac definition, and the text written after
  *by*), `xtext-threshold N`.  To add `lra`, write `Ltac my_lra := timeout
  2 lra.` then `Elpi Accumulate xtext.db lp:{{ xtext-tactic "my_lra" "lra".
  }}`.  To change the threshold, write `:before "xtext-threshold"
  xtext-threshold 50 :- !.`
- Limits: a subproof that a tactic closes loses its explanation, even if
  it was written by hand (e.g. the inductive step of `Nat.add_assoc` at a
  lower threshold).  The threshold is the only control.  Tactics are run
  in Explain's environment; one not loaded there must be added as above.

### (4) "that is" (thesis 3.3 and 5.2.2, Cast')

When the type a subproof proves (synthesised) differs syntactically
from the type expected at its place (inherited) but Rocq finds them
convertible (`coq.unify-eq`), its conclusion says both: `By h2 we have Inv
E R y z, that is R z y`.  The expected types come from the type of the
function applied (premises of an application, of a constructor) and from
the declared type of the theorem for the whole proof.  The statement now
shows the declared type (`We prove Inv E R x z`, not `R z x`).  A
function whose type is a product only after unfolding gets the unfolded
type too (`By h we have Trans E R, that is forall x0 y0 z0 : E, ...`).
This is any definition, with no list of names.  With it, `Trans_Inv`
reads as Fig. 3.13 of the thesis.

- Limits: the cases of an elimination and the branches of a `match` do
  not get it (their goals are stated from the eliminator).  Many "that is"
  in the setoid-rewriting proofs (`Proper ...`, that is `forall x y, ...`)
  are true but noisy.

### Local definitions

`let u := e in M`, when `e` is not a proof, is now written *Let `u : T :=
e`* (role `{.var}`), the local definition of cyp, so that the steps after
it may use `u`.

### Measurements

All 76 texts, generated with each mechanism alone and with all of them
(`XTEXT_OFF`; generation time is the sum of Rocq's `Time` over the texts):

| mechanisms on | list items | characters | generation time (s) |
|---|---|---|---|
| none | 2916 | 418139 | 11.6 |
| formulas that type-check (3a) | 2916 | 426998 | 14.8 |
| inferable arguments (3b) | 2429 | 346399 | 8.1 |
| tactics (5) | 2163 | 310935 | 14.7 |
| "that is" (4) | 2916 | 431659 | 10.1 |
| all | 1856 | 278197 | 16.1 |

The tactics and the inferable arguments shorten the texts (by 26 % and
17 % in items); the formulas that type-check and "that is" make them
longer (by 2 % and 3 % in characters).  With all four, the texts have
36 % fewer items.  All 76 texts are still generated, in 16 s in all.

Per text: items and characters with no mechanism and with all, and the
generation time with all (switch `native`).

| example | items none → all | chars none → all | time all (s) |
|---|---|---|---|
| identity | 1 → 1 | 272 → 272 | 0.04 |
| S_proof | 6 → 6 | 484 → 484 | 0.01 |
| or_intro_example | 2 → 2 | 475 → 475 | 0.01 |
| or_commut | 8 → 8 | 805 → 805 | 0.01 |
| le_0_m | 8 → 8 | 882 → 882 | 0.01 |
| praeclarum | 11 → 11 | 942 → 942 | 0.02 |
| nearly_reflexive | 11 → 9 | 1075 → 960 | 0.02 |
| drinker | 26 → 25 | 2387 → 2338 | 0.06 |
| and_swap | 3 → 3 | 525 → 525 | 0.04 |
| or_swap | 8 → 8 | 747 → 747 | 0.01 |
| imp_trans | 5 → 5 | 444 → 444 | 0.01 |
| not_not_intro | 4 → 4 | 375 → 404 | 0.01 |
| ex_forall | 7 → 7 | 881 → 881 | 0.03 |
| forall_and | 5 → 5 | 585 → 585 | 0.02 |
| add_0_r | 11 → 11 | 1110 → 1110 | 0.04 |
| le_add_r | 15 → 15 | 1594 → 1594 | 0.08 |
| double_neg_em | 9 → 9 | 715 → 787 | 0.01 |
| plus_n_Sm | 11 → 11 | 1295 → 1295 | 0.07 |
| app_nil_r | 12 → 12 | 1224 → 1236 | 0.05 |
| eq_trans | 3 → 3 | 437 → 437 | 0.02 |
| le_n_S | 8 → 8 | 992 → 992 | 0.07 |
| le_0_n_fix | 11 → 11 | 1048 → 1048 | 0.01 |
| length_app_fix | 15 → 14 | 1676 → 1552 | 0.04 |
| bool_cases | 8 → 8 | 977 → 977 | 0.01 |
| Tauto | 4 → 4 | 417 → 417 | 0.09 |
| Trans_Inv | 5 → 4 | 567 → 661 | 0.01 |
| ABCD | 12 → 12 | 720 → 720 | 0.01 |
| or_com | 8 → 8 | 807 → 807 | 0.01 |
| or_sym_nd | 8 → 8 | 755 → 755 | 0.01 |
| praeclarum_nd | 17 → 13 | 1296 → 1082 | 0.01 |
| ADD0 | 12 → 11 | 1182 → 1114 | 0.02 |
| std_app_assoc | 38 → 36 | 3632 → 3469 | 0.29 |
| std_app_nil_r | 30 → 28 | 2741 → 2633 | 0.11 |
| std_app_comm_cons | 1 → 1 | 380 → 426 | 0.01 |
| std_rev_involutive | 15 → 15 | 1651 → 1661 | 0.04 |
| std_rev_app_distr | 18 → 18 | 2222 → 2222 | 0.06 |
| std_length_rev | 18 → 18 | 2276 → 2286 | 0.07 |
| std_map_app | 15 → 15 | 1945 → 1945 | 0.05 |
| std_map_map | 12 → 12 | 1788 → 1793 | 0.04 |
| std_length_app | 16 → 15 | 1988 → 1908 | 0.04 |
| std_in_app_or | 31 → 31 | 3278 → 3278 | 0.21 |
| std_in_or_app | 69 → 18 | 5983 → 1755 | 0.08 |
| std_in_map | 36 → 36 | 3149 → 3149 | 0.08 |
| std_in_eq | 4 → 4 | 465 → 465 | 0.01 |
| std_in_cons | 4 → 4 | 453 → 453 | 0.01 |
| std_Nat_add_comm | 196 → 85 | 25194 → 11659 | 0.41 |
| std_Nat_add_assoc | 265 → 105 | 35634 → 15181 | 0.42 |
| std_Nat_mul_comm | 196 → 85 | 25202 → 11657 | 0.37 |
| std_Nat_le_trans | 484 → 112 | 80900 → 21247 | 0.51 |
| std_Nat_add_0_r | 138 → 104 | 16997 → 14066 | 0.45 |
| std_Nat_add_succ_r | 202 → 87 | 26069 → 12046 | 0.47 |
| std_Nat_le_refl | 19 → 16 | 1981 → 1784 | 0.04 |
| std_Nat_lt_irrefl | 42 → 35 | 5707 → 4457 | 0.12 |
| std_Nat_mul_1_r | 118 → 89 | 14492 → 12345 | 0.37 |
| std_Nat_pred_succ | 1 → 1 | 301 → 338 | 0.01 |
| std_plus_n_O | 12 → 11 | 1161 → 1093 | 0.02 |
| std_plus_n_Sm | 12 → 11 | 1312 → 1222 | 0.03 |
| std_andb_comm | 16 → 16 | 1568 → 1568 | 0.02 |
| std_orb_comm | 16 → 16 | 1563 → 1563 | 0.02 |
| std_negb_involutive | 6 → 6 | 700 → 700 | 0.01 |
| std_andb_true_r | 6 → 6 | 676 → 676 | 0.04 |
| std_orb_false_r | 6 → 6 | 681 → 681 | 0.01 |
| std_andb_assoc | 36 → 36 | 3838 → 3838 | 0.06 |
| std_negb_andb | 16 → 16 | 1785 → 1785 | 0.03 |
| std_and_comm | 11 → 11 | 1055 → 1091 | 0.02 |
| std_or_comm | 21 → 21 | 1536 → 1572 | 0.02 |
| std_and_assoc | 21 → 21 | 1898 → 1946 | 0.05 |
| std_or_assoc | 39 → 39 | 3063 → 3111 | 0.05 |
| std_eq_sym | 2 → 2 | 425 → 425 | 0.01 |
| std_eq_trans | 2 → 2 | 399 → 399 | 0.01 |
| std_f_equal | 2 → 2 | 464 → 464 | 0.01 |


## Contraction, eliminations by their type, proofs in progress

### (2) Contraction of application steps (thesis 3.4.2, Fig. 3.11-3.13)

A modus ponens step lists its premises as dashed subproofs.  A premise
that is itself an application step (`We deduce B`, `In particular ...`),
used only there, can be **contracted**: its own premises take its place,
and its conclusion disappears.  This is the thesis's "contraction de
l'application" (Fig. 3.11), applied to the text.  Three strategies:

- `none`: no contraction (the texts of the previous rounds);
- `maximal`: every such premise is contracted (the thesis's maximal
  contraction, Fig. 3.12);
- `guarded` (default): a premise is contracted only if (1) the step still
  follows from its new premises, checked by one of the tactics of
  `xtext-guard-tactic` (cyp's default ones: `tauto`, `congruence`, `lia`,
  `firstorder`, `auto`, 1 s each).  The tactic that closes the last
  accepted configuration becomes the step's justification (`We deduce C
  *by auto*`), so that cyp runs the same tactic.  (2) Its line has no "that
  is", so
  no conversion step is hidden (the thesis's guarded contraction keeps the
  type expressions that belong to a conversion, Fig. 3.13).

Parameters: the switch `contraction` (see "Switches") and, in `xtext.db`,
`xtext-guard-tactic Ltac Text`.  The decision is greedy, premise by premise,
in the order of the text.

Limits:
- Only application steps are contracted, not the rules for
  constructors, eliminations or rewriting.
- The guard is checked with the premises of the step only, not with all
  the claims before it as cyp does.  It is conservative.
- Contraction can repeat a line: `ABCD` reads `By h4 we have A` four
  times.
- On propositional proofs `tauto` always succeeds, so guarded is maximal
  there; the two differ on arithmetic and rewriting (`Nat.*`).

Example, `ABCD` (Fig. 5.6 of the thesis has the three intermediate
results `P1`, `P2`, `P3`): with contraction, the text is the eight uses
of hypotheses (12 items become 9) and `We deduce D`.  The thesis keeps the
three named intermediate results, which xtext's contraction drops.

### (6) Elimination principles recognised by their type (thesis 6.4.2)

A constant is an elimination principle if its type has this shape, with
no condition on its name:
- parameters;
- a motive `P`, whose type ends in `Prop`;
- between them and the object, binders that are branches (their
  conclusion is `P` applied) or indices (not propositions);
- the eliminated object, of an inductive type `I`;
- a conclusion that is `P` applied to the object (kind 2) or `P` (kind 1:
  the object is a proof).

The type of the object must not mention `P`.  Without this condition,
`proj1 : forall A B, A /\ B -> A` would be read as an elimination with
motive `A`.  Induction hypotheses are still the branch binders whose type
mentions `P`.

Tests (`elim_type.v`):
- `half_le` is proved by `induction n using strong_induction`, a
  course-of-values principle defined in the file: `By definition of nat
  (strong_induction), ...`, with `Assume by induction hypothesis forall
  m, m < n0 -> m / 2 <= m (IH)`.
- `even_or_odd` uses `two_step` (`P 0 -> P 1 -> (forall n, P n -> P (S
  (S n))) -> forall n, P n`, as `list_2_ind` in 6.4.2): `by induction
  (nat, two_step)`, Case 1 (base), Case 2 (base), Case 3 (inductive).

No regression: with `none`, the 76 earlier texts are the same, byte for
byte, as before this round.

### (8) Proofs in progress (L. Théry's thesis, 3.3.3)

`Explain_partial.` (or `Explain_partial to "f.md".`), inside a proof,
prints the text of the proof so far.  Each open goal is written `Prove
G` at its place, as the thesis's `Prouvez G`.  The open goals are the holes
of the partial proof term; their statements are their types.

Limit: rocq-elpi gives the partial proof term only to a command that
closes the proof, so `Explain_partial` ends the proof, as `Abort` does.
In an editor, undo it to go on.

Tests (`partial.v`, texts `examples/*_partial*.md`):
- `or_swap_partial`, after `destruct`: two cases, each `Prove B \/ A`;
- `add_0_r_partial`, after `induction` and the base case: the inductive
  case is `Prove S m + 0 = S m`;
- `praeclarum_partial1` and `2`, the session of section 3.3.3: after
  `split`, `Prove z` and `Prove t`, then `So by definition of and (conj)`,
  as the thesis's `Prouvez z / Prouvez t / Ceci réuni donne z ∧ t`.  After
  the first conjunct, `We deduce z` (from `Hx` and `Hxz`) and `Prove t`.

### Measurements

All 78 texts (the 76 earlier ones and the two of `elim_type.v`), with each
contraction strategy.  The generation time is the sum of Rocq's `Time`
over the texts; the guard costs it.

| strategy | list items | characters | generation time (s) |
|---|---|---|---|
| none | 1919 | 288045 | 13.6 |
| maximal | 1720 | 267311 | 13.6 |
| guarded | 1818 | 279926 | 33.5 |

Texts that change with the strategy:

| example | items none / maximal / guarded | chars none → guarded |
|---|---|---|
| S_proof | 6 / 5 / 5 | 484 → 466 |
| nearly_reflexive | 9 / 8 / 8 | 960 → 936 |
| imp_trans | 5 / 4 / 4 | 444 → 426 |
| length_app_fix | 14 / 13 / 13 | 1552 → 1495 |
| ABCD | 12 / 9 / 9 | 720 → 638 |
| praeclarum_nd | 13 / 11 / 11 | 1082 → 1042 |
| std_app_assoc | 36 / 35 / 35 | 3469 → 3382 |
| std_app_nil_r | 28 / 27 / 27 | 2633 → 2552 |
| std_length_app | 15 / 14 / 14 | 1908 → 1849 |
| std_in_map | 36 / 34 / 34 | 3149 → 3045 |
| std_Nat_add_comm | 85 / 66 / 75 | 11659 → 10948 |
| std_Nat_add_assoc | 105 / 82 / 93 | 15181 → 14188 |
| std_Nat_mul_comm | 85 / 66 / 75 | 11657 → 10946 |
| std_Nat_le_trans | 112 / 73 / 110 | 21247 → 21059 |
| std_Nat_add_0_r | 104 / 82 / 91 | 14066 → 13115 |
| std_Nat_add_succ_r | 87 / 68 / 75 | 12046 → 11167 |
| std_Nat_le_refl | 16 / 15 / 15 | 1784 → 1730 |
| std_Nat_lt_irrefl | 35 / 28 / 32 | 4457 → 4298 |
| std_Nat_mul_1_r | 89 / 70 / 80 | 12345 → 11719 |
| half_le | 36 / 29 / 30 | 6438 → 5345 |
| even_or_odd | 27 / 27 / 27 | 3410 → 3410 |


- `maximal` contracts more steps of the `Nat.*` texts than `guarded`;
  a contracted step that cyp's tactics cannot close becomes one more red
  step, which is why `guarded` is the default.

The texts in progress (`*_partial*.md`) have one `Prove G` step per open
goal.  They are not counted above.

## Checking the texts with cyp

`sh cyprun.sh LIMIT name...` copies each text to `cyp-check/`, adds a
`flags:` line to its header (so that `Require Import XText.<file>`
finds the example files), and runs cyp's driver (`cyp/bin/cyp.ml`, which runs
`Cyp File` in the switch `elpi4`; `CYP_LIB` the directory where
`cyp/vernac/Cyp.v` is compiled), one text at a time, under `nice`, with
at most 8 GB of memory per text.  It prints, per text, the time and the
list items proved / not proved / not checked (`cyp-check/results.tsv`).

All 82 texts, 300 s per text:

- 73 texts are checked: 933 steps proved, 29 not proved, 220 not checked
  (lines with no claim: `Let`, `Assume`, the announcement of a proof by
  cases);
- 9 time out: the 5 texts of the private case study, `half_le`,
  `std_in_app_or`, `std_Nat_add_0_r`, `std_Nat_le_trans` (two of the
  private ones grow to 12-16 GB before the limit);
- the 29 steps not proved: 14 closing steps of a `match` (no
  justification: `destruct` is tactic code), 4 closing steps of a
  `list_ind` elimination, 5 constructor steps `*by ex_intro*` (cyp applies
  `ex_intro` and cannot find the witness), the recursive call of
  `length_app_fix` (it states the theorem itself), and 5 steps of a
  private text (rewritings and `ring` certificates) that cyp's default
  tactics do not close;
- 13 texts have every step proved but cyp stops at the end with an
  anomaly, `Universe CypRules.cyp_check.N undefined` (`app_nil_r`,
  `std_app_assoc`, `std_rev_involutive`, ...): a formula with `Type` in
  it (`forall (A0 : Type) ...`, the statement of a theorem used) makes a
  universe that the proof cyp builds does not declare.  This is in cyp,
  not in the texts;
- cyp proves each claim again with its own tactics, so a green step says
  that the claim follows, not that it follows the way the text says.

The texts in the other languages (12 per language, 9 languages) give the
same results, step by step, as the English ones (same roles and statuses
in each `.cyp.json`): 90 steps proved, 4 not proved, 30 not checked per
language (`cyp-check/results_fr_it.tsv`, `cyp-check/results_langs.tsv`).

## The staged translation (thesis chapters 2 and 3, `elpi/staged.elpi`)

With the switch `translation` set to `staged` (variable
`XTEXT_TRANSLATION=staged`), a proof becomes text in the three stages of
Coscoy's thesis, each a predicate on its own data type, so that each can
be read against its figure:

1. **annotation** (3.3.4, Fig. 3.9, `annotate`): each node of the proof
   term gets its *constrained* type Tc (what it proves, partly
   synthesised, 3.3.1) and its *required* type Tr (what is left to prove,
   inherited from the statement, 3.3.2), one clause per rule (Var, Const,
   Abs, App1, App2).  The helpers (synthesis of types, Fig. 3.4; equality
   of type expressions; the required type of the whole proof) are in
   `elpi/type-expressions.elpi`, the weak head normal form (Fig. 3.3) is
   `whnf` (`elpi/printing.elpi`);
2. **contraction** (2.3, and its guarded form, 3.4.2, Fig. 3.11,
   `contract`): nested applications and series of abstractions are
   merged.  The switch `contraction` (variable `XTEXT_CONTRACTION`):
   `none`, `maximal` (every contraction of 2.3) or `guarded` (only the
   contractions that drop a single annotation, so that no conversion step
   disappears);
3. **writing** (2.3.3, Fig. 2.10 for applications; 3.4.1, `write`): a
   conclusion says Tc, then `, that is` Tr when they differ (the thesis's
   "ce qui est équivalent à").

The forms that the thesis treats only in chapter 6 (eliminations,
introductions, rewriting, `fix`) and `let`, `match`, casts are written by
the direct writer; their subproofs come back to the stages.

**Trans_Inv**, Fig. 3.10 of the thesis (doubly annotated, not
contracted), is `examples-staged-none/Trans_Inv.md`: the five double
annotations L1-L5 of the figure are at the same steps,

```markdown
- By h we have `Trans E R`, that is `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`.  [L1]
- By h2 we have `Inv E R y z`, that is `R z y`.                                          [L2]
- By h1 we have `Inv E R x y`, that is `R y x`.                                          [L3]
- By application, we have `R z x`, that is `Inv E R x z`.                                [L4]
- We have proved `forall x0 y z : E, ...`, that is `Trans E (Inv E R)`.                 [L5]
```

with, as in the figure, one sentence per abstraction and per application
(`By application, we have R z y -> R y x -> R z x`) and one for each
element that is not a proof (`The element z belongs to E`).  Fig. 3.12
(maximal contraction) is `examples-staged-maximal/Trans_Inv.md`
(`Applying h to z, y, x, h2 and h1, we have R z x, that is Inv E R x
z`), Fig. 3.13 (guarded contraction) `examples-staged-guarded/Trans_Inv.md`.

An earlier version computed the same double annotation in one pass, as
hooks in the direct writer (switch `xtext-annotation`, texts
`examples-double/`); it was removed in favour of the stages, which give
the same annotations (it is in the history, commit 56a84ef).

## Not done

- The section "Further optimizations" of the paper (one-use
  assumptions, `Trivially`, `A fortiori`, dependence analysis).
- The specific wordings of the paper's figures for the usual connectives
  and classical reasoning (`Altogether`, `Obviously`, `If we have ...
  Otherwise`).
- From the thesis: leaving out the generalised predicate (6.4.1), and
  its other chapters (type annotations, reversible scripts).
- Mutual fixpoints (`mfix`) and `cofix` are left unchanged, as are
  non-propositional subterms.
- The `require` line of the header is fixed (Arith, Lia, List and the
  file of the theorem); the load path for cyp is added by `cyprun.sh`.
