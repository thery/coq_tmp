---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# or_assoc

Let `A B C : Prop`{.var}. We prove `(A \/ B) \/ C <-> A \/ B \/ C`{.claim}.

- We have proved `(A \/ B) \/ C -> A \/ B \/ C`{.claim}.
  - Assume `(A \/ B) \/ C`{.hyp} (H).
    - We prove `A \/ B \/ C`{.fact} by case analysis on `(A \/ B) \/ C`{.fact} (H) (or, match):
    - Case 1: we prove `A \/ B -> A \/ B \/ C`{.claim}.
      - Assume `A \/ B`{.hyp} (H0).
        - We prove `A \/ B \/ C`{.fact} by case analysis on `A \/ B`{.fact} (H0) (or, match):
        - Case 1.1: we prove `A -> A \/ B \/ C`{.claim}.
          - Assume `A`{.hyp} (H1).
            - By definition of or (or_introl), from `A`{.fact} (H1) we deduce `A \/ B \/ C`{.claim} *by eapply @or_introl; eauto*.
        - Case 1.2: we prove `B -> A \/ B \/ C`{.claim}.
          - Assume `B`{.hyp} (H1).
            - By definition of or (or_introl), from `B`{.fact} (H1) we deduce `B \/ C`{.claim} *by eapply @or_introl; eauto*.
            - By definition of or (or_intror), we have `A \/ B \/ C`{.claim} *by eapply @or_intror; eauto*.
        - We have `A \/ B \/ C`{.claim} in all cases.
    - Case 2: we prove `C -> A \/ B \/ C`{.claim}.
      - Assume `C`{.hyp} (H0).
        - By definition of or (or_intror), from `C`{.fact} (H0) we deduce `B \/ C`{.claim} *by eapply @or_intror; eauto*.
        - By definition of or (or_intror), we have `A \/ B \/ C`{.claim} *by eapply @or_intror; eauto*.
    - We have `A \/ B \/ C`{.claim} in all cases.
- We have proved `A \/ B \/ C -> (A \/ B) \/ C`{.claim}.
  - Assume `A \/ B \/ C`{.hyp} (H).
    - We prove `(A \/ B) \/ C`{.fact} by case analysis on `A \/ B \/ C`{.fact} (H) (or, match):
    - Case 1: we prove `A -> (A \/ B) \/ C`{.claim}.
      - Assume `A`{.hyp} (H0).
        - By definition of or (or_introl), from `A`{.fact} (H0) we deduce `A \/ B`{.claim} *by eapply @or_introl; eauto*.
        - By definition of or (or_introl), we have `(A \/ B) \/ C`{.claim} *by eapply @or_introl; eauto*.
    - Case 2: we prove `B \/ C -> (A \/ B) \/ C`{.claim}.
      - Assume `B \/ C`{.hyp} (H0).
        - We prove `(A \/ B) \/ C`{.fact} by case analysis on `B \/ C`{.fact} (H0) (or, match):
        - Case 2.1: we prove `B -> (A \/ B) \/ C`{.claim}.
          - Assume `B`{.hyp} (H1).
            - By definition of or (or_intror), from `B`{.fact} (H1) we deduce `A \/ B`{.claim} *by eapply @or_intror; eauto*.
            - By definition of or (or_introl), we have `(A \/ B) \/ C`{.claim} *by eapply @or_introl; eauto*.
        - Case 2.2: we prove `C -> (A \/ B) \/ C`{.claim}.
          - Assume `C`{.hyp} (H1).
            - By definition of or (or_intror), from `C`{.fact} (H1) we deduce `(A \/ B) \/ C`{.claim} *by eapply @or_intror; eauto*.
        - We have `(A \/ B) \/ C`{.claim} in all cases.
    - We have `(A \/ B) \/ C`{.claim} in all cases.
- So by definition of and (conj), we have `((A \/ B) \/ C -> A \/ B \/ C) /\ (A \/ B \/ C -> (A \/ B) \/ C)`{.claim} *by eapply @conj; eauto*, that is `(A \/ B) \/ C <-> A \/ B \/ C`{.fact}.
