<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# or_assoc

❌ Let `A B C : Prop`. We prove `((A \/ B) \/ C -> A \/ B \/ C) /\ (A \/ B \/ C -> (A \/ B) \/ C)`.

<details><summary>not proved</summary>

```
1 goal
  
  A, B, C : Prop
  H : (A \/ B) \/ C -> A \/ B \/ C
  H0 : A \/ B \/ C -> (A \/ B) \/ C
  H1 : ((A \/ B) \/ C -> A \/ B \/ C) /\ (A \/ B \/ C -> (A \/ B) \/ C)
  ============================
  ((A \/ B) \/ C -> A \/ B \/ C) /\ (A \/ B \/ C -> (A \/ B) \/ C)

File "./cyp_ko_26.v", line 4, characters 0-168:
Error: No applicable tactic.
```

</details>

- ✅ We have proved `(A \/ B) \/ C -> A \/ B \/ C`.
  - ▫️ Assume `(A \/ B) \/ C` (H).
    - ▫️ We prove `A \/ B \/ C` by case analysis on `(A \/ B) \/ C` (H) (or, match):
    - ✅ Case 1: we prove `A \/ B -> A \/ B \/ C`.
      - ▫️ Assume `A \/ B` (H0).
        - ▫️ We prove `A \/ B \/ C` by case analysis on `A \/ B` (H0) (or, match):
        - ✅ Case 1.1: we prove `A -> A \/ B \/ C`.
          - ▫️ Assume `A` (H1).
            - ✅ By definition of or (or_introl), from `A` (H1) we deduce `A \/ B \/ C` .*by eapply @or_introl; eauto*
        - ✅ Case 1.2: we prove `B -> A \/ B \/ C`.
          - ▫️ Assume `B` (H1).
            - ✅ By definition of or (or_introl), from `B` (H1) we deduce `B \/ C` .*by eapply @or_introl; eauto*
            - ✅ By definition of or (or_intror), we have `A \/ B \/ C` .*by eapply @or_intror; eauto*
        - ✅ We have `A \/ B \/ C` in all cases.
    - ✅ Case 2: we prove `C -> A \/ B \/ C`.
      - ▫️ Assume `C` (H0).
        - ✅ By definition of or (or_intror), from `C` (H0) we deduce `B \/ C` .*by eapply @or_intror; eauto*
        - ✅ By definition of or (or_intror), we have `A \/ B \/ C` .*by eapply @or_intror; eauto*
    - ✅ We have `A \/ B \/ C` in all cases.
- ✅ We have proved `A \/ B \/ C -> (A \/ B) \/ C`.
  - ▫️ Assume `A \/ B \/ C` (H).
    - ▫️ We prove `(A \/ B) \/ C` by case analysis on `A \/ B \/ C` (H) (or, match):
    - ✅ Case 1: we prove `A -> (A \/ B) \/ C`.
      - ▫️ Assume `A` (H0).
        - ✅ By definition of or (or_introl), from `A` (H0) we deduce `A \/ B` .*by eapply @or_introl; eauto*
        - ✅ By definition of or (or_introl), we have `(A \/ B) \/ C` .*by eapply @or_introl; eauto*
    - ✅ Case 2: we prove `B \/ C -> (A \/ B) \/ C`.
      - ▫️ Assume `B \/ C` (H0).
        - ▫️ We prove `(A \/ B) \/ C` by case analysis on `B \/ C` (H0) (or, match):
        - ✅ Case 2.1: we prove `B -> (A \/ B) \/ C`.
          - ▫️ Assume `B` (H1).
            - ✅ By definition of or (or_intror), from `B` (H1) we deduce `A \/ B` .*by eapply @or_intror; eauto*
            - ✅ By definition of or (or_introl), we have `(A \/ B) \/ C` .*by eapply @or_introl; eauto*
        - ✅ Case 2.2: we prove `C -> (A \/ B) \/ C`.
          - ▫️ Assume `C` (H1).
            - ✅ By definition of or (or_intror), from `C` (H1) we deduce `(A \/ B) \/ C` .*by eapply @or_intror; eauto*
        - ✅ We have `(A \/ B) \/ C` in all cases.
    - ✅ We have `(A \/ B) \/ C` in all cases.
- ✅ So by definition of and (conj), we have `((A \/ B) \/ C -> A \/ B \/ C) /\ (A \/ B \/ C -> (A \/ B) \/ C)` .*by eapply @conj; eauto*

