---
require: From Stdlib Require Import ZArith Reals Lra Lia.
scope: R_scope
by: lra
rules: forall_premise.v
---

# forall_premise

A lemma with a premise on all the integers, `forall k : Z, ...`,
closed by lia in a context of many facts on reals: lia reads none of
them (lia_guard counts only the hypotheses lia reads, prooftext/Tactics.v).

Let `x y : R`{.var} and `j : Z`{.var}. If `x = IZR (j * 2 ^ 4 - -5)`{.hyp},
`Rabs x <= 12`{.hyp} and `0 < y`{.hyp} then `Rabs x <= 11`{.claim}.

- First `0 < y + 1`{.claim},
- then `0 < y + 2`{.claim},
- then `0 < y + 3`{.claim},
- then `0 < y + 4`{.claim},
- then `0 < y + 5`{.claim},
- then `0 < y + 6`{.claim},
- then `0 < y + 7`{.claim},
- then `0 < y + 8`{.claim},
- then `0 < y + 9`{.claim},
- then `0 < y + 10`{.claim},
- then `0 < y + 11`{.claim},
- then `0 < y + 12`{.claim},
- then `0 < y + 13`{.claim},
- then `0 < y + 14`{.claim},
- then `0 < y + 15`{.claim},
- then `0 < y + 16`{.claim},
- The integer `j * 2 ^ 4 - -5` is 16 j + 5, at most 12 in absolute
  value, so 5 or -11, thus `Rabs x <= 11`{.claim}. *grid_bound*{.just}
