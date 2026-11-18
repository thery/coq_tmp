---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# or_com

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (H). We prove `B \/ A`{.claim}.

- We prove `B \/ A`{.fact} by case analysis on `A \/ B`{.fact} (H) (or, or_ind):
- Case 1: we prove `A -> B \/ A`{.claim}.
  - Assume `A`{.hyp} (H0).
    - By definition of or (or_intror), from `A`{.fact} (H0) we deduce `B \/ A`{.claim} *by eapply @or_intror; eauto*.
- Case 2: we prove `B -> B \/ A`{.claim}.
  - Assume `B`{.hyp} (H0).
    - By definition of or (or_introl), from `B`{.fact} (H0) we deduce `B \/ A`{.claim} *by eapply @or_introl; eauto*.
- We have `B \/ A`{.claim} in all cases *by eapply (@or_ind (A) (B) (B \/ A)); cbv beta; eauto*.
