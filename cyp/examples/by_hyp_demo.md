---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# by_hyp_demo

Let `A B : Prop`{.var}. Let `P Q : nat -> Prop`{.var}. Let `n : nat`{.var}. Assume `A`{.hyp} (ha), `A -> B`{.hyp} (hab), `forall m, m <= n -> P m`{.hyp} (hp) and `forall m, P m -> B -> Q m`{.hyp} (hq). We prove `Q n`{.claim}.

- By modus ponens on *hab*{.just}, `B`{.claim}.
- By *hp*{.just} we have `n <= n -> P n`{.claim}.
- So, by the step before (*c2*{.just}), `P n`{.claim}.
- Hence `Q n`{.claim}, by *hq*{.just}.
