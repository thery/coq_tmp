---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# and_assoc

✅ Let `A B C : Prop`{.var}. We prove `(A /\ B) /\ C <-> A /\ B /\ C`{.claim}.

- ✅ We have proved `(A /\ B) /\ C -> A /\ B /\ C`{.claim}.
  - ▫️ Assume `(A /\ B) /\ C`{.hyp} (H).
    - ✅ Going back to the definition of and (match) in `(A /\ B) /\ C`{.fact} (H), we prove `A /\ B /\ C`{.claim}:
      - ▫️ Assume `A /\ B`{.hyp} (H0) and `C`{.hyp} (h).
        - ✅ Going back to the definition of and (match) in `A /\ B`{.fact} (H0), we prove `C -> A /\ B /\ C`{.claim}:
          - ▫️ Assume `A`{.hyp} (H1), `B`{.hyp} (H00) and `C`{.hyp} (H10).
            - ✅ By H1 we have `A`{.claim}.
            - ✅ By definition of and (conj), from `B`{.fact} (H00) and `C`{.fact} (H10) we deduce `B /\ C`{.claim} *by Corelib.Init.Logic.conj*.
            - ✅ So by definition of and (conj), we have `A /\ B /\ C`{.claim} *by Corelib.Init.Logic.conj*.
        - ✅ By application, with h, we have `A /\ B /\ C`{.claim}.
- ✅ We have proved `A /\ B /\ C -> (A /\ B) /\ C`{.claim}.
  - ▫️ Assume `A /\ B /\ C`{.hyp} (H).
    - ✅ Going back to the definition of and (match) in `A /\ B /\ C`{.fact} (H), we prove `(A /\ B) /\ C`{.claim}:
      - ▫️ Assume `A`{.hyp} (H0) and `B /\ C`{.hyp} (H00).
        - ✅ Going back to the definition of and (match) in `B /\ C`{.fact} (H00), we prove `(A /\ B) /\ C`{.claim}:
          - ▫️ Assume `B`{.hyp} (H01) and `C`{.hyp} (H1).
            - ✅ By definition of and (conj), from `A`{.fact} (H0) and `B`{.fact} (H01) we deduce `A /\ B`{.claim} *by Corelib.Init.Logic.conj*.
            - ✅ By H1 we have `C`{.claim}.
            - ✅ So by definition of and (conj), we have `(A /\ B) /\ C`{.claim} *by Corelib.Init.Logic.conj*.
- ✅ So by definition of and (conj), we have `((A /\ B) /\ C -> A /\ B /\ C) /\ (A /\ B /\ C -> (A /\ B) /\ C)`{.claim} *by Corelib.Init.Logic.conj*.
