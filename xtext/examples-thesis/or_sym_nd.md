---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# or_sym_nd

Let `a b : Prop`{.var}. Assume `a \/ b`{.hyp} (H1). We prove `b \/ a`{.claim}.

- We prove `b \/ a`{.fact} by case analysis on `a \/ b`{.fact} (H1) (or, match):
- Case 1: we prove `a -> b \/ a`{.claim}.
  - Assume `a`{.hyp} (H2).
    - By definition of or (or_intror), from `a`{.fact} (H2) we deduce `b \/ a`{.claim} *by eapply @or_intror; eauto*.
- Case 2: we prove `b -> b \/ a`{.claim}.
  - Assume `b`{.hyp} (H3).
    - By definition of or (or_introl), from `b`{.fact} (H3) we deduce `b \/ a`{.claim} *by eapply @or_introl; eauto*.
- We have `b \/ a`{.claim} in all cases.
