<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.paper. -->

# or_commut

✅ Let `A B : Prop`. Assume `A \/ B` (h). We prove `B \/ A`.

- ▫️ We prove `B \/ A` by case analysis on `A \/ B` (h) (or, or_ind):
- ✅ Case 1: we prove `A -> B \/ A`.
  - ▫️ Assume `A` (i).
    - ▫️ By definition of or (or_intror), from `A` (i) we deduce `B \/ A` .*by eapply @or_intror; eauto*
- ✅ Case 2: we prove `B -> B \/ A`.
  - ▫️ Assume `B` (j).
    - ▫️ By definition of or (or_introl), from `B` (j) we deduce `B \/ A` .*by eapply @or_introl; eauto*
- ✅ We have `B \/ A` in all cases.

