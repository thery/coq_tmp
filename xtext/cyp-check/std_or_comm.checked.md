---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_comm

✅ Let `A B : Prop`{.var}. We prove `A \/ B <-> B \/ A`{.claim}.

- ✅ We have proved `A \/ B -> B \/ A`{.claim}.
  - ▫️ Assume `A \/ B`{.hyp} (H).
    - ▫️ We prove `B \/ A`{.fact} by case analysis on `A \/ B`{.fact} (H) (or, match):
    - ✅ Case 1: we prove `A -> B \/ A`{.claim}.
      - ▫️ Assume `A`{.hyp} (H0).
        - ✅ By definition of or (or_intror), from `A`{.fact} (H0) we deduce `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
    - ✅ Case 2: we prove `B -> B \/ A`{.claim}.
      - ▫️ Assume `B`{.hyp} (H0).
        - ✅ By definition of or (or_introl), from `B`{.fact} (H0) we deduce `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
    - ✅ We have `B \/ A`{.claim} in all cases.
- ✅ We have proved `B \/ A -> A \/ B`{.claim}.
  - ▫️ Assume `B \/ A`{.hyp} (H).
    - ▫️ We prove `A \/ B`{.fact} by case analysis on `B \/ A`{.fact} (H) (or, match):
    - ✅ Case 1: we prove `B -> A \/ B`{.claim}.
      - ▫️ Assume `B`{.hyp} (H0).
        - ✅ By definition of or (or_intror), from `B`{.fact} (H0) we deduce `A \/ B`{.claim} *by Corelib.Init.Logic.or_intror*.
    - ✅ Case 2: we prove `A -> A \/ B`{.claim}.
      - ▫️ Assume `A`{.hyp} (H0).
        - ✅ By definition of or (or_introl), from `A`{.fact} (H0) we deduce `A \/ B`{.claim} *by Corelib.Init.Logic.or_introl*.
    - ✅ We have `A \/ B`{.claim} in all cases.
- ✅ So by definition of and (conj), we have `(A \/ B -> B \/ A) /\ (B \/ A -> A \/ B)`{.claim} *by Corelib.Init.Logic.conj*, that is `A \/ B <-> B \/ A`{.fact}.
