<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.lemmas. -->

# or_swap

✅ Let `A B : Prop`. Assume `A \/ B` (H). We prove `B \/ A`.

- ▫️ We prove `B \/ A` by case analysis on `A \/ B` (H) (or, match):
- ✅ Case 1: we prove `A -> B \/ A`.
  - ▫️ Assume `A` (a).
    - ▫️ By definition of or (or_intror), from `A` (a) we deduce `B \/ A` .*by eapply @or_intror; eauto*
- ✅ Case 2: we prove `B -> B \/ A`.
  - ▫️ Assume `B` (b).
    - ▫️ By definition of or (or_introl), from `B` (b) we deduce `B \/ A` .*by eapply @or_introl; eauto*
- ✅ We have `B \/ A` in all cases.

