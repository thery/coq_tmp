---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# errors

✅ Let `n : nat`{.var}. Assume `n <= 3`{.hyp} (h). We prove `n <= 5`{.claim}.

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
