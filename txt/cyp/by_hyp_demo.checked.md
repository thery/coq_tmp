---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# by_hyp_demo

✅ Let `A B : Prop`. Let `P Q : nat -> Prop`. Let `n : nat`. Assume `A` (ha), `A -> B` (hab), `forall m, m <= n -> P m` (hp) and `forall m, P m -> B -> Q m` (hq). We prove `Q n`.

- ✅ By modus ponens, `B`. *by hab*
- ✅ We have `n <= n -> P n`. *by hp*
- ✅ So `P n`. *by c2*
- ✅ Hence `Q n`. *by hq*
