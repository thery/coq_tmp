<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# and_comm

✅ Let `A B : Prop`. We prove `(A /\ B -> B /\ A) /\ (B /\ A -> A /\ B)`.

- ✅ We have proved `A /\ B -> B /\ A`.
  - ▫️ Assume `A /\ B` (H).
    - ✅ Going back to the definition of and (match) in `A /\ B` (H), we prove `B /\ A`:
      - ▫️ Assume `A` (H0) and `B` (H00).
        - ✅ By definition of and (conj), from `B` (H00) and `A` (H0) we deduce `B /\ A` .*by eapply @conj; eauto*
- ✅ We have proved `B /\ A -> A /\ B`.
  - ▫️ Assume `B /\ A` (H).
    - ✅ Going back to the definition of and (match) in `B /\ A` (H), we prove `A /\ B`:
      - ▫️ Assume `B` (H0) and `A` (H00).
        - ✅ By definition of and (conj), from `A` (H00) and `B` (H0) we deduce `A /\ B` .*by eapply @conj; eauto*
- ✅ So by definition of and (conj), we have `(A /\ B -> B /\ A) /\ (B /\ A -> A /\ B)` .*by eapply @conj; eauto*

