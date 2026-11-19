---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# errors_demo

✅ Let `n : nat`{.var}. Assume `n <= 3`{.hyp} (h). We prove `n <= 5`{.claim}.

- ▫️ A remark: nothing here is tagged, `n` included; it is shown, not checked.
- ❌ From `n <= 4`{.fact} we have `n <= 6`{.claim}.

  <details><summary>the fact n <= 4 is no hypothesis or conclusion visible here</summary></details>

- ❌ By *no_such_lemma*{.just} we have `n <= 7`{.claim}.

  <details><summary>no_such_lemma names nothing known: no hypothesis, node, lemma, rule or tactic</summary></details>

- ❌ Assume `n = 0`{.hyp} (k).

  <details><summary>line 13: a node with no conclusion: it has tags, but no {.claim}</summary></details>

  - ✅ We have `n <= 1`{.claim} by *k*{.just} and *lia*{.just}.
- ❌ By *k*{.just} we have `n <= 8`{.claim}.

  <details><summary>line 15: k is out of scope here</summary></details>

- ✅ Hence `n <= 5`{.claim}, by *h*{.just} and *lia*{.just}.
