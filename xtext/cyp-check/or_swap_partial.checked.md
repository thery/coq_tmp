<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial. -->

# or_swap_partial (proof in progress)

✅ Let `A B : Prop`. Assume `A \/ B` (H). We prove `B \/ A`.

- ▫️ We prove `B \/ A` by case analysis on `A \/ B` (H) (or, match):
- ✅ Case 1: we prove `A -> B \/ A`.
  - ▫️ Assume `A` (a).
    - ✅ Prove `B \/ A`.
- ✅ Case 2: we prove `B -> B \/ A`.
  - ▫️ Assume `B` (b).
    - ✅ Prove `B \/ A`.
- ✅ We have `B \/ A` in all cases.

