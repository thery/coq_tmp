# One implementation of cyp: the design

Step 2 of the cleaning session (see REVIEW.md).  A proposal: nothing is
changed until it is agreed.

## The idea

cyp's semantics (what a step means, how it is checked) is written once, in
Rocq-Elpi, and everything else uses it: the Markdown proofs (`Cyp File`),
the vernacular form (`Cyp Lemma`), the command line and the editor, and
xtext, which writes texts that cyp reads back.

```
                 vocabulary (en, fr, it)          rules (.elpi) + lemmas (.v)
                        |        \                         |
   proof.md --> Cyp File --> cyp core (Elpi) <-- Cyp Lemma |
                        |        |                         |
                        |    checked proof: proof.checked.md, proof.cyp.json
                        |                                  |
           command line / VS Code (thin driver)   xtext (Explain) writes proof.md
```

## The parts

**1. The core (`cyp_core.elpi`).**  The only place that says what a proof
means:
- a step is words and formulas; a formula is a claim, a hypothesis, a
  variable or a mention, by the last role phrase before it, or by a tag
  `{.role}`; a formula that is not a proposition is a mention (asked to
  Rocq, not guessed from its text);
- a backward step: the last role phrase before its claim is a backward
  phrase;
- local scopes (*Let `x : T`*, *Assume `P`*, nested or for the following
  steps) and local definitions (*Let `u := e`*);
- each step proved when it is read, in its own context; names: the
  hypotheses of the statement H1, H2, ... (or the name written after them,
  `(h)`), the claims c1, c2, ...;
- the justification `*by X*`: the rules named X, else the lemma X, else the
  tactic named X; code is a tactic; no justification: all the rules, then
  the default tactics;
- conjunctions and disjunctions split by cyp; premises of an applied lemma
  closed by the rules or the default tactics;
- the lemma is defined only when every step is proved.

**2. The vocabulary (`vocab/en.elpi`, `fr.elpi`, `it.elpi`).**  One table
per language, used both ways:
- for reading (cyp): role phrases and backward phrases;
- for writing (xtext): one template per kind of sentence ("We have `P`",
  "Let us consider an arbitrary `x : T`", "By `h` we have `P`", ...), with
  slots, so that word order can differ between languages.

What xtext writes is then by construction what cyp reads.

**3. Tactics by name.**  One table `tactic-name "lia" "cyp_std_lia"` and
one set of wrappers, in the cyp library; xtext's tactic database uses the
same names.

**4. Rules and lemmas.**  As now: proved lemmas in compiled libraries
(`float_lemmas.v`), rules in `.elpi` files.  The shared floating-point
rules made general (the predecessor of any power of two, formats of ±2^e,
one precision parameter for `interval`); what is particular to one lemma
in that lemma's files.

**5. The Markdown front end, in Elpi (`Cyp File`).**  Reads the header,
title, statement and steps (nested lists), writes `proof.checked.md`
(✅/❌, the goal and Rocq's message under a ❌) and `proof.cyp.json` (the
same for the editor: lines, roles, status, messages).

**6. `Cyp Lemma`** stays as the vernacular form: the same core, the body
as a list of strings and terms instead of a file.

**7. The command line and VS Code.**  The OCaml program keeps no
semantics: it writes a two-line `.v` (the header's `require:` and
`Elpi CypFile "proof.md"`), runs `rocq c` on it and passes on the JSON.
The VS Code extension reads that JSON, as today.  The default command is a
setting, not a path written in the code.

## What becomes of the findings

| finding | resolved by |
|---|---|
| A1 three copies of the semantics | part 1 |
| A2 separate vocabularies | part 2 |
| A3 tactics by name three times | part 3 |
| B1 `_format` in the claim test | part 1 (asked to Rocq) |
| B2 particular numbers in the shared rules | part 4 |
| B3 `i_prec 130` three times | part 4 |
| B4 rewriting by names | xtext, with round 6 (eliminators by type) |
| B5 thresholds in the code | xtext parameters, documented |
| B6 English inside xtext's rules | part 2 |
| B7 arbitrary defaults | part 5: no default `require:`/`by:` |
| B8 absolute path in VS Code | part 7 |
| B9 names of hypotheses | part 1 |
| B10 *written as* claim and backward | part 2 |
| C1 text pasted, messages parsed | parts 5 and 7 |
| C2 Cyp File behind the OCaml cyp | part 5 (nested steps, scopes) |
| D  READMEs | rewritten for the current design only |

## What it costs, and what is lost

- **Everything runs in the switch `elpi4`** (Elpi 4.0 and Rocq-Elpi with
  `coq.parse.argument`) until that API is released.  xtext, today in
  `native` (Elpi 3.7), moves to `elpi4` too, since it shares the
  vocabulary: its Elpi code needs the small Elpi 4 fixes cyp needed (typed
  higher-order arguments).
- **The cache of proved steps** (the OCaml cyp's) goes: inside Rocq each
  run checks every step.  A failing step costs its time limit, which becomes
  a parameter per proof (`timeout:`).  Make-style caching per file remains.
- **The OCaml cyp is kept unchanged until the Elpi version passes all the
  checks below**, then reduced to the driver of part 7.

## The checks, before and after

- the proofs of the private case study;
- cyp's examples (square_pos, rules_demo, named_demo, features, the French
  and Italian square_pos);
- xtext's 76 texts: generation, and cyp's counts per text.

## Decisions (2026-11-17)

1. One implementation in Elpi; the OCaml program becomes the thin driver
   of part 7, kept unchanged until the Elpi version passes all the checks.
2. xtext moves to the switch `elpi4`.
3. The cache of proved steps is dropped.
4. `Cyp Lemma` is kept, as well as `Cyp File`.

## Order of the work

- 3a, now: the Elpi core reaches the OCaml cyp's features (nested steps,
  local scopes and definitions, tags, names, vocabulary files for en, fr,
  it, the checked Markdown and the JSON), checked on cyp's examples and the
  private case study in `elpi4`.
- 3b, when the agents' rounds are over: xtext moves to `elpi4` and writes
  with the vocabulary; the OCaml program becomes the driver; the shared
  floating-point rules made general; the READMEs rewritten.

## Status of 3a (2026-11-17)

The Elpi core is in cyp/vernac (Cyp.v and elpi/: text, vocab_en/fr/it,
check, proof, markdown), run by the driver script cyp/vernac/cyprun.py, in
the switch elpi4.  Checked, same results as the OCaml cyp:

| proof | OCaml cyp (native) | Elpi core (elpi4) |
|---|---|---|
| the proofs of the private case study | proved | proved, same steps |
| examples: square_pos | 6/7 (one wrong on purpose) | 1 of 7 not proved |
| rules_demo, named_demo, features, by_lemma_demo, apply_demo | proved | proved |
| square_pos in French and in Italian | proved | proved |
| a nested-scope demo (vernac/scope_demo.md) | -- | proved |

Not possible yet: a justification written as tactic code (*by destruct b;
cbn; eauto*), which xtext writes: Rocq-Elpi cannot turn a string into a
tactic (coq.parse.argument does not accept ltac_tactic:(...), and
"(ltac:(...))" raw is not implemented).  For the same reason the default
tactics are called through one table of Ltac wrappers in Cyp.v.
