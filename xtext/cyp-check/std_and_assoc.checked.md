<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# and_assoc

✅ Let `A B C : Prop`. We prove `((A /\ B) /\ C -> A /\ B /\ C) /\ (A /\ B /\ C -> (A /\ B) /\ C)`.

- ✅ We have proved `(A /\ B) /\ C -> A /\ B /\ C`.
  - ▫️ Assume `(A /\ B) /\ C` (H).
    - ✅ Going back to the definition of and (match) in `(A /\ B) /\ C` (H), we prove `A /\ B /\ C`:
      - ▫️ Assume `A /\ B` (H0) and `C` (h).
        - ✅ By h we have `C`.
        - ✅ Going back to the definition of and (match) in `A /\ B` (H0), we prove `C -> A /\ B /\ C`:
          - ▫️ Assume `A` (H1) and `B` (H00) and `C` (H10).
            - ✅ By H1 we have `A`.
            - ✅ By definition of and (conj), from `B` (H00) and `C` (H10) we deduce `B /\ C` .*by eapply @conj; eauto*
            - ✅ So by definition of and (conj), we have `A /\ B /\ C` .*by eapply @conj; eauto*
        - ✅ We deduce `A /\ B /\ C`.
- ✅ We have proved `A /\ B /\ C -> (A /\ B) /\ C`.
  - ▫️ Assume `A /\ B /\ C` (H).
    - ✅ Going back to the definition of and (match) in `A /\ B /\ C` (H), we prove `(A /\ B) /\ C`:
      - ▫️ Assume `A` (H0) and `B /\ C` (H00).
        - ✅ Going back to the definition of and (match) in `B /\ C` (H00), we prove `(A /\ B) /\ C`:
          - ▫️ Assume `B` (H01) and `C` (H1).
            - ✅ By definition of and (conj), from `A` (H0) and `B` (H01) we deduce `A /\ B` .*by eapply @conj; eauto*
            - ✅ By H1 we have `C`.
            - ✅ So by definition of and (conj), we have `(A /\ B) /\ C` .*by eapply @conj; eauto*
- ✅ So by definition of and (conj), we have `((A /\ B) /\ C -> A /\ B /\ C) /\ (A /\ B /\ C -> (A /\ B) /\ C)` .*by eapply @conj; eauto*

