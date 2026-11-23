---
require: From Stdlib Require Import Arith Lia.
---

# justifications

✅ Let `P Q : nat -> Prop`{.var} and `n : nat`{.var}. Assume `forall m, m <= n -> P m`{.hyp} (hp) and `forall m, P m -> Q m`{.hyp} (hq). We prove `Q (n + 0) /\ n * 1 = n`{.claim}.

- ✅ By *hp*{.just} we have `n <= n -> P n`{.claim}.
- ✅ So, by the step before (*c1*{.just}), `P n`{.claim} (pn).
- ✅ Applying *hq*{.just} to *pn*{.just}, we have `Q n`{.claim} (qn).
- ✅ By the lemma *Nat.add_0_r*{.just}, `n + 0 = n`{.claim} (e).
- ✅ With *e*{.just} and *qn*{.just}, we get `Q (n + 0)`{.claim} (qn0).
- ✅ By the tactic *lia*{.just}, `n * 1 = n`{.claim} (m1).
- ✅ By *qn0*{.just} and *m1*{.just}, we conclude `Q (n + 0) /\ n * 1 = n`{.claim}.
