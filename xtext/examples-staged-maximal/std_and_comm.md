---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# and_comm

Let `A B : Prop`{.var}. We prove `A /\ B <-> B /\ A`{.claim}.

- We have proved `A /\ B -> B /\ A`{.claim}.
  - Assume `A /\ B`{.hyp} (H).
    - Going back to the definition of and (match) in `A /\ B`{.fact} (H), we prove `B /\ A`{.claim}:
      - Assume `A`{.hyp} (H0) and `B`{.hyp} (H00).
        - By definition of and (conj), from `B`{.fact} (H00) and `A`{.fact} (H0) we deduce `B /\ A`{.claim} *by Corelib.Init.Logic.conj*.
- We have proved `B /\ A -> A /\ B`{.claim}.
  - Assume `B /\ A`{.hyp} (H).
    - Going back to the definition of and (match) in `B /\ A`{.fact} (H), we prove `A /\ B`{.claim}:
      - Assume `B`{.hyp} (H0) and `A`{.hyp} (H00).
        - By definition of and (conj), from `A`{.fact} (H00) and `B`{.fact} (H0) we deduce `A /\ B`{.claim} *by Corelib.Init.Logic.conj*.
- So by definition of and (conj), we have `(A /\ B -> B /\ A) /\ (B /\ A -> A /\ B)`{.claim} *by Corelib.Init.Logic.conj*.
