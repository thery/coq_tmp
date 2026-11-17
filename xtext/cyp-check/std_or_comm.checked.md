<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# or_comm

✅ Let `A B : Prop`. We prove `A \/ B <-> B \/ A`.

- ✅ We have proved `A \/ B -> B \/ A`.
  - ▫️ Assume `A \/ B` (H).
    - ▫️ We prove `B \/ A` by case analysis on `A \/ B` (H) (or, match):
    - ✅ Case 1: we prove `A -> B \/ A`.
      - ▫️ Assume `A` (H0).
        - ✅ By definition of or (or_intror), from `A` (H0) we deduce `B \/ A` .*by eapply @or_intror; eauto*
    - ✅ Case 2: we prove `B -> B \/ A`.
      - ▫️ Assume `B` (H0).
        - ✅ By definition of or (or_introl), from `B` (H0) we deduce `B \/ A` .*by eapply @or_introl; eauto*
    - ✅ We have `B \/ A` in all cases.
- ✅ We have proved `B \/ A -> A \/ B`.
  - ▫️ Assume `B \/ A` (H).
    - ▫️ We prove `A \/ B` by case analysis on `B \/ A` (H) (or, match):
    - ✅ Case 1: we prove `B -> A \/ B`.
      - ▫️ Assume `B` (H0).
        - ✅ By definition of or (or_intror), from `B` (H0) we deduce `A \/ B` .*by eapply @or_intror; eauto*
    - ✅ Case 2: we prove `A -> A \/ B`.
      - ▫️ Assume `A` (H0).
        - ✅ By definition of or (or_introl), from `A` (H0) we deduce `A \/ B` .*by eapply @or_introl; eauto*
    - ✅ We have `A \/ B` in all cases.
- ✅ So by definition of and (conj), we have `(A \/ B -> B \/ A) /\ (B \/ A -> A \/ B)` , that is `A \/ B <-> B \/ A`.*by eapply @conj; eauto*

