---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# and_assoc

Let `A B C : Prop`{.var}. We prove `(A /\ B) /\ C <-> A /\ B /\ C`{.claim}.

- We have proved `(A /\ B) /\ C -> A /\ B /\ C`{.claim}.
  - Assume `(A /\ B) /\ C`{.hyp} (H). Going back to the definition of *and*{.just} (*match*{.just}) in *H*{.just}, we prove `A /\ B /\ C`{.claim}:
    - Assume `A /\ B`{.hyp} (H0) and `C`{.hyp} (h).
      - By *h*{.just} we have `C`{.claim}.
      - Going back to the definition of *and*{.just} (*match*{.just}) in *H0*{.just}, we prove `C -> A /\ B /\ C`{.claim}:
        - Assume `A`{.hyp} (H1), `B`{.hyp} (H00) and `C`{.hyp} (H10).
          - By *H1*{.just} we have `A`{.claim}.
          - By definition of and (*conj*{.just}), from *H00*{.just} and *H10*{.just} we deduce `B /\ C`{.claim}.

          So by definition of and (*conj*{.just}), we have `A /\ B /\ C`{.claim}.

      We deduce `A /\ B /\ C`{.claim}.
- We have proved `A /\ B /\ C -> (A /\ B) /\ C`{.claim}.
  - Assume `A /\ B /\ C`{.hyp} (H). Going back to the definition of *and*{.just} (*match*{.just}) in *H*{.just}, we prove `(A /\ B) /\ C`{.claim}:
    - Assume `A`{.hyp} (H0) and `B /\ C`{.hyp} (H00). Going back to the definition of *and*{.just} (*match*{.just}) in *H00*{.just}, we prove `(A /\ B) /\ C`{.claim}:
      - Assume `B`{.hyp} (H01) and `C`{.hyp} (H1).
        - By definition of and (*conj*{.just}), from *H0*{.just} and *H01*{.just} we deduce `A /\ B`{.claim}.
        - By *H1*{.just} we have `C`{.claim}.

        So by definition of and (*conj*{.just}), we have `(A /\ B) /\ C`{.claim}.
- So by definition of and (*conj*{.just}), we have `((A /\ B) /\ C -> A /\ B /\ C) /\ (A /\ B /\ C -> (A /\ B) /\ C)`, that is `(A /\ B) /\ C <-> A /\ B /\ C`{.claim}.
