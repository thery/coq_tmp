---
require: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# or_swap

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (H). We prove `B \/ A`{.claim}.

- We prove `B \/ A`{.fact} by case analysis on `A \/ B`{.fact} (H) (or, match):
- Case 1: we prove `A -> B \/ A`{.claim}.
  - Assume `A`{.hyp} (a).
    - By definition of or (or_intror), from `A`{.fact} (a) we deduce `B \/ A`{.claim} *by eapply @or_intror; eauto*.
- Case 2: we prove `B -> B \/ A`{.claim}.
  - Assume `B`{.hyp} (b).
    - By definition of or (or_introl), from `B`{.fact} (b) we deduce `B \/ A`{.claim} *by eapply @or_introl; eauto*.
- We have `B \/ A`{.claim} in all cases.
