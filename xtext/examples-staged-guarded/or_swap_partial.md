---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial.
by: tauto | congruence | lia | firstorder | auto
---

# or_swap_partial (proof in progress)

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (H). We prove `B \/ A`{.claim}.

- We prove `B \/ A`{.fact} by case analysis on `A \/ B`{.fact} (H) (or, match):
- Case 1: we prove `A -> B \/ A`{.claim}.
  - Assume `A`{.hyp} (a).
    - Prove `B \/ A`{.claim}.
- Case 2: we prove `B -> B \/ A`{.claim}.
  - Assume `B`{.hyp} (b).
    - Prove `B \/ A`{.claim}.
- We have `B \/ A`{.claim} in all cases.
