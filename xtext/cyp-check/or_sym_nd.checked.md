<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# or_sym_nd

✅ Let `a b : Prop`. Assume `a \/ b` (H1). We prove `b \/ a`.

- ▫️ We prove `b \/ a` by case analysis on `a \/ b` (H1) (or, match):
- ✅ Case 1: we prove `a -> b \/ a`.
  - ▫️ Assume `a` (H2).
    - ✅ By definition of or (or_intror), from `a` (H2) we deduce `b \/ a` .*by eapply @or_intror; eauto*
- ✅ Case 2: we prove `b -> b \/ a`.
  - ▫️ Assume `b` (H3).
    - ✅ By definition of or (or_introl), from `b` (H3) we deduce `b \/ a` .*by eapply @or_introl; eauto*
- ✅ We have `b \/ a` in all cases.

