# Writing a proof in cyp: a tutorial, part 2

This is the second part of the tutorial: what happens when something is
wrong, the Rocq commands, xtext, a reference card, and how the tutorial
is checked.  The first part, [TUTORIAL.md](TUTORIAL.md), goes from the
idea to the justifications.

## 7. When something is wrong

An error never stops cyp.  The step with the error is not tried, it is
marked ❌ with the reason, and the steps after it still use its
conclusion.  [tutorial/ch11_errors.md](tutorial/ch11_errors.md) has one
mistake per step:

<!-- tutorial: ch11_errors.md -->
```markdown
---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# errors

Let `n : nat`{.var}. Assume `n <= 3`{.hyp} (h). We prove `n <= 5`{.claim}.

- We have `n <= 2`{.claim}.
- By *no_such_lemma*{.just} we have `n <= 6`{.claim}.
- From `n <= 1`{.fact} we have `n <= 7`{.claim}.
- Assume `n = 0`{.hyp} (k).
  - By *k*{.just}, `n <= 1`{.claim}.
- By *k*{.just} we have `n <= 8`{.claim}.
- We prove `n <= 9`{.claim}:
  - We have `n <= 4`{.claim}.

  So `n <= 9`{.claim}.
- We have `n <= 10`{.clam}.
- We have `n <=`{.claim}.
- Hence `n <= 5`{.claim}, by *h*{.just}.
```

<!-- tutorial: expected/cyp/ch11_errors.checked.md -->
```markdown
- ❌ We have `n <= 2`{.claim}.

  <details><summary>not proved: n <= 2</summary></details>

- ❌ By *no_such_lemma*{.just} we have `n <= 6`{.claim}.

  <details><summary>no_such_lemma names nothing known: no hypothesis, node, lemma or declared justification word (declare it: CypJustification "no_such_lemma" := tactic. or := rules.)</summary></details>

- ❌ From `n <= 1`{.fact} we have `n <= 7`{.claim}.

  <details><summary>the fact n <= 1 is no hypothesis or conclusion visible here</summary></details>

- ❌ Assume `n = 0`{.hyp} (k).

  <details><summary>line 13: a node with no conclusion: it has tags, but no {.claim}</summary></details>

  - ✅ By *k*{.just}, `n <= 1`{.claim}.
- ❌ By *k*{.just} we have `n <= 8`{.claim}.

  <details><summary>line 15: k is out of scope here</summary></details>

- ❌ We prove `n <= 9`{.claim}:

  <details><summary>line 16: a node with two conclusions, n <= 9 and n <= 9</summary></details>

  - ✅ We have `n <= 4`{.claim}.

  So `n <= 9`{.claim}.
- ❌ We have `n <= 10`{.clam}.

  <details><summary>line 20: an unknown class, {.clam}; line 20: a node with no conclusion: it has tags, but no {.claim}</summary></details>

- ❌ We have `n <=`{.claim}.

  <details><summary>does not parse: Syntax error: [term] expected after '<=' (in [term]).</summary></details>

- ✅ Hence `n <= 5`{.claim}, by *h*{.just}.
```

One by one:

1. **A false claim**: "not proved", and the goal.
2. **An unknown name**: the message says how to declare a word.
3. **A fact that is not known**: nothing in scope is `n <= 1`.
4. **A step with no conclusion**: it has a hypothesis but no claim.  Its
   sub-step is still checked (✅), but the step gives nothing to the steps
   after it.  To fix it, put a claim in the item or in a closing
   paragraph, as in [section 4](TUTORIAL.md#4-structure-steps-sub-steps-scope).
5. **A name out of scope**: `k` holds only inside step 4.
6. **Two conclusions**: "We prove `n <= 9`{.claim}" up front *and* "So
   `n <= 9`{.claim}" in the closing paragraph.  Tag one of them only; the
   other is plain text.
7. **An unknown class**: `{.clam}` is a typo; the step then has no claim
   either.
8. **A formula that does not parse**: Rocq's message.

The last step is ✅: it uses the conclusions of the steps before it, even
the wrong ones.  The program prints

<!-- tutorial: expected/cyp/ch11_errors.out -->
```
cyp: errors
Error:
cyp: 8 of 12 steps of errors not proved (1, 2, 3, 4, 5, 6, 7, 8), see cyp-tutorial/ch11_errors.checked.md
exit 1
```

**The exit code of the program `cyp`**: 0 when the lemma is defined
(every step proved), 1 when it is not (a step not proved, an error, or a
statement that cannot be read), 2 when it cannot run (wrong usage,
`CYP_LIB` not set).  It always writes the checked text and, with
`--json`, a JSON file with the status of every step (for editors).

**Cyp File and Cyp Lemma always succeed**, and leave goals.  In Rocq,
`Cyp File` (two words, section 8) does not fail on these errors: each step
with a conclusion that cyp did not prove becomes a goal of the Proof
block.  [tutorial/ch11_errors.v](tutorial/ch11_errors.v) shows them with
`Show.`:

<!-- tutorial: expected/rocq/ch11_errors.out -->
```
cyp: errors, 12 steps, 4 condition(s) left for the Proof block: 1, 2, 3, 5
  🔶 condition 1: n <= 2
  🔶 condition 2: n <= 6
  🔶 condition 3: n <= 7
  🔶 condition 5: n <= 8
4 goals (?c1)
  
  n : nat
  h : n <= 3
  ============================
  n <= 2

goal 2 (?c2) is:
 n <= 6
goal 3 (?c3) is:
 n <= 7
goal 4 (?c5) is:
 n <= 8
```

Steps 4, 6, 7 and 8 have no conclusion that can be read, so they give no
goal.  The commands fail only when the statement itself cannot be read.

Try it in the browser:
<https://thery.github.io/rocq-web/?example=cyp-tutorial&file=ch11_errors.v>.

## 8. The Rocq side: Cyp File and Cyp Lemma

cyp lives inside Rocq ([vernac/](vernac/README.md)); the program `cyp` only
writes a small Rocq file and runs it.  There are three commands.

- `CypFile "proof.md".` checks the text, writes `proof.checked.md`, and
  defines the lemma when every step is proved; otherwise it fails.  This
  is what the program `cyp` runs.  It does not run the header's
  `require:` and `rules:` lines: the Rocq file does them itself.
- `Cyp File "proof.md".` (two words) is followed by a **Proof block**.
  Each condition that cyp did not prove, and each open goal, is a goal of
  the block, named after its step: `?c1` for step 1, `?c2_1` for step 2.1.
  `[c1]: tac.` proves it by its name, in any order; `CypQed.` ends the
  proof (not `Qed.`).
- `Cyp Lemma name binders : statement := [ steps ].` is the same proof
  written as a Rocq command, with no Markdown file.

### Cyp File with a Proof block

[tutorial/ch12_goals.md](tutorial/ch12_goals.md) has a step that the
default tactic `lia` cannot prove (it knows nothing of `Z.sqrt`), and an
open goal:

<!-- tutorial: ch12_goals.md -->
```markdown
---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
---

# goals

Let `a b : Z`{.var}. Assume `0 <= a`{.hyp} and `0 <= b`{.hyp}. We prove `0 <= Z.sqrt a + Z.sqrt b + a`{.claim}.

- We have `0 <= Z.sqrt a`{.claim}.
- Prove `0 <= Z.sqrt b`{.goal}.
- Hence `0 <= Z.sqrt a + Z.sqrt b + a`{.claim}.
```

(`scope: Z_scope` reads the formulas in that notation scope.)
[tutorial/ch12_goals.v](tutorial/ch12_goals.v):

<!-- tutorial: ch12_goals.v -->
```coq
From Stdlib Require Import ZArith Lia.
From CypV Require Import Cyp.
Open Scope Z_scope.

Cyp File "cyp-tutorial/ch12_goals.md".
Proof.
  Show.
  [c2]: apply Z.sqrt_nonneg.
  [c1]: apply Z.sqrt_nonneg.
CypQed.
Check goals.
```

Rocq prints

<!-- tutorial: expected/rocq/ch12_goals.out -->
```
cyp: goals
  ✅ 0
  ✅ 3
cyp: goals, 4 steps, 2 condition(s) left for the Proof block: 1, 2
  🔶 condition 1: 0 <= Z.sqrt a
  🔶 open goal 2 of the text: 0 <= Z.sqrt b
2 goals (?c1)
  
  a, b : Z
  H1 : 0 <= a
  H2 : 0 <= b
  ============================
  0 <= Z.sqrt a

goal 2 (?c2) is:
 0 <= Z.sqrt b
cyp: goals proved
goals
     : forall a b : Z, 0 <= a -> 0 <= b -> 0 <= Z.sqrt a + Z.sqrt b + a
exit 0
```

and the checked text marks the two steps 🔶 with their numbers:

<!-- tutorial: expected/rocq/ch12_goals.checked.md -->
```markdown
- 🔶 **[1]** We have `0 <= Z.sqrt a`{.claim}.

  <details><summary>condition 1, to prove in the Proof block: 0 <= Z.sqrt a</summary></details>

- 🔶 **[2]** Prove `0 <= Z.sqrt b`{.goal}.

  <details><summary>open goal of the text, not tried: condition 2, to prove in the Proof block: 0 <= Z.sqrt b</summary></details>

- ✅ Hence `0 <= Z.sqrt a + Z.sqrt b + a`{.claim}.
```

The program `cyp` has no Proof block: on this text it marks step 1 ❌ and
step 2 🔶, and exits with 1.  A text and a Proof block together give a
proof where the easy steps are checked by cyp and the hard ones are
proved by tactics.

Try it in the browser:
<https://thery.github.io/rocq-web/?example=cyp-tutorial&file=ch12_goals.v>.

### Cyp Lemma

The proof of [section 2](TUTORIAL.md#2-a-first-proof) as a Rocq command,
[tutorial/ch13_lemma.v](tutorial/ch13_lemma.v):

<!-- tutorial: ch13_lemma.v -->
```coq
From Stdlib Require Import Arith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope pstring_scope.

Cyp Lemma double_gt' (n : nat) (h : 0 < n) : n < 2 * n :=
  [ "From" (0 < n) "{.fact} we get" (n + 0 < n + n) "{.claim}." ;
    "This is" (n < 2 * n) "{.claim}." ].
Proof. CypQed.
Check double_gt'.

(* A false step: cyp leaves it as the goal ?c1, which nothing proves. *)
Cyp Lemma wrong (n : nat) (h : 0 < n) : n < 2 * n :=
  [ "We have" (2 * n < n) "{.claim}." ;
    "Hence" (n < 2 * n) "{.claim}." ].
Proof.
  Show.
  Fail lia.
Abort.
```

The binders of the statement are the variables and hypotheses; the body
is the list of steps.  In a step, words are strings, formulas are Rocq
terms, and the string after a formula starts with its class.  A list
among the parts of a step is the list of its sub-steps.
`"{.claim} by *lia*{.just}."` gives a formula its class and the step a
justification.  The second lemma leaves its false step as the goal `?c1`:

<!-- tutorial: expected/rocq/ch13_lemma.out -->
```
cyp: wrong, 3 steps, 1 condition(s) left for the Proof block: 1
  🔶 condition 1: 2 * n < n
1 goal (?c1)
  
  n : nat
  h : 0 < n
  ============================
  2 * n < n
```

Try it in the browser:
<https://thery.github.io/rocq-web/?example=cyp-tutorial&file=ch13_lemma.v>.

**Timing.**  With the environment variable `CYP_TIME` set, cyp prints the
time spent on each condition (`cyp: time 2.1 1234 ms`).

## 9. Writing a text from a Rocq proof: xtext

The other way round, [xtext](../xtext/README.md) turns a Rocq proof into
text: `ExtractText foo.` prints the proof of the lemma `foo` in English
(or in nine other languages), and `ExtractText foo to "foo.md".` writes it
as a cyp text, every formula tagged with its role and every justification
tagged `{.just}`.  `ExtractText_partial` does the same for a proof stopped
midway, its open goals tagged `{.goal}`.  cyp can check such a text again
(the texts of [../xtext/cyp-check/](../xtext/cyp-check)), and the text can
then be edited by hand like any other.  For example, the proof of
`and_swap` becomes:

<!-- tutorial: ../../xtext/cyp-check/and_swap.md -->
```markdown
# and_swap

Let `A B : Prop`{.var}. Assume `A /\ B`{.hyp} (H). We prove `B /\ A`{.claim}.

- Going back to the definition of *and*{.just} (*match*{.just}) in *H*{.just}, we prove `B /\ A`{.claim}:
  - Assume `A`{.hyp} (a) and `B`{.hyp} (b). By definition of and (*conj*{.just}), from *b*{.just} and *a*{.just} we deduce `B /\ A`{.claim}.
```

## 10. Reference card

**Tags**

| written | role | what cyp does |
|---|---|---|
| `` `x y : T`{.var} `` | variables | in scope in the step and its sub-steps |
| `` `u := e`{.var} `` | local definition | the same, `u` unfolds to `e` |
| `` `A`{.hyp} (h) `` | hypothesis, named `h` (else `H1`, `H2`, ...) | in scope in the step and its sub-steps |
| `` `C`{.claim} (n) `` | conclusion of the step, named `n` (else `c2`, `c2_1`) | proved; one per step |
| `` `G`{.goal} `` | open goal: a conclusion left to prove | not tried; a goal of the Proof block |
| `` `F`{.fact} `` | a formula the step uses | checked to be known, put first |
| `*X*{.just}` | justification: a name | see the order below |
| `` `F` ``, `*X*`, any word | plain text | shown, not used |
| an item with no tag | remark | shown (▫️), not checked |

**Steps**: a list item (with its sub-items and closing paragraph), a span
`[ ... ]{.p}`, or a div `::: p` ... `:::`.

**Justification order**: `match`, `induction` → a name of the text in
scope (hypothesis, step, variable) → a word declared by `CypJustification`
→ a lemma → error.  With no justification: rules, `by:` tactics, `tauto
lia nia lra`, then the gap tactic.

**Header fields**

| field | meaning |
|---|---|
| `require:` | Rocq text run before the proof (the program `cyp`) |
| `scope:` | the notation scope of the formulas |
| `by:` | default tactics, separated by `|` |
| `rules:` | rule files (`.v`, `.elpi`), relative to the text |
| `flags:` | options of `rocq c` (`-Q dir Name`; `${VAR}` for an environment variable) |
| `lang:` | the language of cyp's messages (`en`, `fr`, `it`) |
| `gaps: off` | no gap tactic |

**Commands**

| command | what it does |
|---|---|
| `cyp proof.md` | checks, writes `proof.checked.md`; exit 0 / 1 / 2 |
| `cyp --conditions proof.md` | prints the conditions, tries nothing |
| `cyp --json proof.md` | also writes `proof.cyp.json` |
| `CypFile "proof.md".` | the same in Rocq; fails if a step is not proved |
| `#[bare] CypFile "proof.md".` | prints the conditions |
| `Cyp File "proof.md". Proof. [c1]: tac. CypQed.` | the conditions left are goals `?cN` |
| `Cyp Lemma n binders : T := [ steps ]. Proof. ... CypQed.` | the proof as a Rocq command |
| `#[gaps="off"]` | no gap tactic, on `Cyp File` and `Cyp Lemma` |
| `CypJustification "w" := tac.` / `:= rules.` | declares a justification word |
| `../prooftext/pdf.sh [--html] proof.checked.md` | the PDF (or web page) |

**Marks**: checked Markdown ✅ ❌ 🔶 ▫️; PDF ✔ ✘ ◆ ▫.

## 11. Keeping the tutorial true

The examples are in [tutorial/](tutorial): for each example NN, the text
`chNN_*.md` and a Rocq file `chNN_*.v` that explains it in comments and
runs it (`CypFile`, `Cyp File`, `Cyp Lemma`).  The Rocq files name their
texts `"cyp-tutorial/chNN_*.md"`, as rocq-web needs (Rocq runs there from
the root of the files).

[tutorial/check.sh](tutorial/check.sh) copies the directory to a
temporary `cyp-tutorial/`, runs the program `cyp` on every text and Rocq
on every chapter file (from the parent directory, as in rocq-web), and
compares what they print and the checked texts with
[tutorial/expected/](tutorial/expected).  It also checks that each block
of the two pages marked with its file is an exact excerpt of that file.

```sh
sh tutorial/check.sh            # compare; exit 1 on a difference
sh tutorial/check.sh --update   # rewrite expected/ after a change
```

[tutorial/rocq-web.sh](tutorial/rocq-web.sh) installs the examples in a
rocq-web checkout: `sh tutorial/rocq-web.sh ROCQWEB/app/public/examples`
copies them to the example folder `cyp-tutorial` and adds its entry to
`index.json`.
