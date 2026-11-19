---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# or_assoc

Let `A B C : Prop`{.var}. We prove `(A \/ B) \/ C <-> A \/ B \/ C`{.claim}.

- We have proved `(A \/ B) \/ C -> A \/ B \/ C`{.claim}.
  - Assume `(A \/ B) \/ C`{.hyp} (H). We prove `A \/ B \/ C` by case analysis on *H*{.just} (or, match):
    - Case 1: we prove `A \/ B -> A \/ B \/ C`{.claim}.
      - Assume `A \/ B`{.hyp} (H0). We prove `A \/ B \/ C` by case analysis on *H0*{.just} (or, match):
        - Case 1.1: we prove `A -> A \/ B \/ C`{.claim}.
          - Assume `A`{.hyp} (H1). By definition of or (*or_introl*{.just}), from *H1*{.just} we deduce `A \/ B \/ C`{.claim}.
        - Case 1.2: we prove `B -> A \/ B \/ C`{.claim}.
          - Assume `B`{.hyp} (H1).
            - By definition of or (*or_introl*{.just}), from *H1*{.just} we deduce `B \/ C`{.claim}.

            By definition of or (*or_intror*{.just}), we have `A \/ B \/ C`{.claim}.

        We have `A \/ B \/ C`{.claim} in all cases.
    - Case 2: we prove `C -> A \/ B \/ C`{.claim}.
      - Assume `C`{.hyp} (H0).
        - By definition of or (*or_intror*{.just}), from *H0*{.just} we deduce `B \/ C`{.claim}.

        By definition of or (*or_intror*{.just}), we have `A \/ B \/ C`{.claim}.

    We have `A \/ B \/ C`{.claim} in all cases.
- We have proved `A \/ B \/ C -> (A \/ B) \/ C`{.claim}.
  - Assume `A \/ B \/ C`{.hyp} (H). We prove `(A \/ B) \/ C` by case analysis on *H*{.just} (or, match):
    - Case 1: we prove `A -> (A \/ B) \/ C`{.claim}.
      - Assume `A`{.hyp} (H0).
        - By definition of or (*or_introl*{.just}), from *H0*{.just} we deduce `A \/ B`{.claim}.

        By definition of or (*or_introl*{.just}), we have `(A \/ B) \/ C`{.claim}.
    - Case 2: we prove `B \/ C -> (A \/ B) \/ C`{.claim}.
      - Assume `B \/ C`{.hyp} (H0). We prove `(A \/ B) \/ C` by case analysis on *H0*{.just} (or, match):
        - Case 2.1: we prove `B -> (A \/ B) \/ C`{.claim}.
          - Assume `B`{.hyp} (H1).
            - By definition of or (*or_intror*{.just}), from *H1*{.just} we deduce `A \/ B`{.claim}.

            By definition of or (*or_introl*{.just}), we have `(A \/ B) \/ C`{.claim}.
        - Case 2.2: we prove `C -> (A \/ B) \/ C`{.claim}.
          - Assume `C`{.hyp} (H1). By definition of or (*or_intror*{.just}), from *H1*{.just} we deduce `(A \/ B) \/ C`{.claim}.

        We have `(A \/ B) \/ C`{.claim} in all cases.

    We have `(A \/ B) \/ C`{.claim} in all cases.
- So by definition of and (*conj*{.just}), we have `((A \/ B) \/ C -> A \/ B \/ C) /\ (A \/ B \/ C -> (A \/ B) \/ C)`{.claim}.
