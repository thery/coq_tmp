# Review of cyp and xtext: what is ad hoc, duplicated or fragile

Step 1 of the cleaning session: findings only, nothing changed.  Reviewed:
cyp at main (bin/cyp.ml, rules/cyp_rules.v, vernac/Cyp.v, vernac/CypFile.v,
exp/float_lemmas.v and the .elpi rules, vscode/), xtext at 40d1b6d
(xtext.elpi, Explain.v).  The rounds the agents are doing now (cyp: Lemma 3;
xtext: 2/6/8) are not included.

## A. The same thing done in several places

**A1. cyp's semantics exists three times, and the copies already differ.**
- `bin/cyp.ml` (OCaml): role words (en/fr/it), backward phrases, the test
  "a formula with no relation is a mention", local scopes and definitions,
  how a step's goal is built.
- `rules/cyp_rules.v` (Elpi, for the Markdown cyp): closing a goal with the
  rules, `named` rules, `apply`, the justification `*by X*` (`cyp_justify`).
- `vernac/Cyp.v` (Elpi, for `Cyp Lemma` and `Cyp File`): its own copy of
  closing a goal, `named`, `apply`, the justification (`try-close`), and its
  own role words.

Differences already there: the vernacular role words have *as* and *for*
(not in OCaml), OCaml has *where*, *written as*, *obtain*...; the backward
words are phrases in OCaml (*equivalent to prove*) and single words in
Elpi (*equivalent*, *written*); the standard tactics a step may name are
not the same list (`ring`, `field`, `reflexivity` only in the Markdown cyp).

**A2. cyp and xtext have separate vocabularies.**  xtext writes phrases
("We have", "Let us consider an arbitrary", "We have proved", "since `x` is
arbitrary") that cyp must read back with its own role words; it works
because the words happen to match ("since" gives a fact, "let" a variable).
Nothing ties the two lists together, and the multilingual round will need
both in three languages.

**A3. Calling a standard tactic by name from Elpi is solved three times:**
`cyp_std_*` in rules/cyp_rules.v, `cyp_std_*` again in vernac/Cyp.v (a
different list), `xtext_tauto`/`xtext_lia` in xtext's Explain.v.

## B. Ad hoc choices

**B1.** `bin/cyp.ml`, `relation_re`: "a formula is a claim if it contains
`=`, `<`, ..., `forall`, `exists`, `_format`, `True`, `False`".  `_format`
is a name of libm; the vernacular version asks Rocq whether the formula is a
proposition, which is the generic test.

**B2.** `exp/float.elpi` lines 19-30 and `exp/float_lemmas.v` lines 93-145:
rules and lemmas for particular numbers (1 − 2⁻⁵³, 2⁻⁵³, −2⁻⁵⁴, their
predecessors and successors, "below 2⁻⁵³ means at most 2⁻⁵³ − 2⁻¹⁰⁶"),
written for Lemma 1, in the SHARED files.  The general facts exist in Flocq
(format of ±2^e, `pred_bpow`, `succ` of a power of two): one rule that
computes the predecessor of any power of two, and Lemma 1's special point
(`float_exp_mid`, the midpoint at −2⁻⁵⁴) in a file of Lemma 1.

**B3.** `exp/float_lemmas.v` lines 216, 244, 256: `interval with
(i_prec 130)` written three times: one parameter.

**B4.** xtext, `xtext.elpi` lines 376-378 and 864-870: elimination
principles found by their name (`C_ind`, `_rect`, `_sind`), rewriting by a
list of names (`eq_ind`, `eq_rect`, `eq_rec`, `eq_sind` and their `_r`
forms).  Round 6 (now running) recognises eliminations by their type; the
rewriting list should follow the same test (the eliminator of an equality).

**B5.** xtext thresholds: 300 nodes (a parameter, `xtext-threshold`), 60
candidates for the implicit-argument pass (`xtext.elpi` line 156, written
in the code), 2 s per tactic.  All should be parameters, with the reason
for each default.

**B6.** xtext's English sentences are written inside the rules (about 30
places, e.g. lines 422, 463, 475, 544-555).  The multilingual round needs
them in tables anyway: what is said (abstract sentence) apart from how
(phrase per language).

**B7.** `bin/cyp.ml` lines 239-241: default header `require: From Stdlib
Require Import ZArith Lia.` and `by: lia` when a proof says nothing.
Arbitrary; a proof should say what it uses.

**B8.** `vscode/package.json`: the default command is an absolute path in
`/home/thery/...`.

**B9.** Names of hypotheses: the Markdown cyp lets Rocq name them (`H`,
`H0`, ...); the vernacular one names them `H1`, `H2`, ... and the claims
`c1`, `c2`, ...  So `*by H1*` can work in one and not in the other.

**B10.** `bin/cyp.ml`: *written as* is both a claim word and a backward
phrase.

## C. Fragile mechanisms

**C1.** The Markdown cyp checks a proof by pasting its formulas into a
generated `.v` file, compiling it, and reading Rocq's messages back with
regular expressions (which line failed, which goal); a failing step is
compiled once more to get its message.  `Cyp File` does the same inside
Rocq, with real terms and real goals.

**C2.** `Cyp File` has fewer features than the Markdown cyp: no nested
steps, no local scopes (*Let*, *Assume*), no local definitions.  Lemma
"red" and Lemma 2 cannot go through it yet.

## D. Documentation

The READMEs (cyp/README.md, cyp/vernac/README.md, cyp/exp/NOTES-cyp.md,
xtext/README.md) grew round by round and mix the current state with what
was added when; they should describe the current design only.

## The question for step 2

Most of A and C come from having two implementations of cyp.  The design
to decide: **one implementation of cyp's semantics, in Elpi** (Cyp File
and Cyp Lemma), with
- one vocabulary file per language, read by cyp and written by xtext (A2,
  B6, B10);
- one way to name a tactic (A3);
- the Markdown cyp reduced to what Elpi cannot do (the editor, the coloured
  output), or removed once `coq.parse.argument` is in a released Rocq-Elpi.
