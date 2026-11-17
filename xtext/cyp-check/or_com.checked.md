<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# or_com

✅ Let `A B : Prop`. Assume `A \/ B` (H). We prove `B \/ A`.

- ▫️ We prove `B \/ A` by case analysis on `A \/ B` (H) (or, or_ind):
- ✅ Case 1: we prove `A -> B \/ A`.
  - ▫️ Assume `A` (H0).
    - ✅ By definition of or (or_intror), from `A` (H0) we deduce `B \/ A` .*by eapply @or_intror; eauto*
- ✅ Case 2: we prove `B -> B \/ A`.
  - ▫️ Assume `B` (H0).
    - ✅ By definition of or (or_introl), from `B` (H0) we deduce `B \/ A` .*by eapply @or_introl; eauto*
- ✅ We have `B \/ A` in all cases .*by eapply (@or_ind (A) (B) (B \/ A)); cbv beta; eauto*

