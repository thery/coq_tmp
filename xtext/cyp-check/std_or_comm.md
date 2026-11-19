---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_comm

Let `A B : Prop`{.var}. We prove `A \/ B <-> B \/ A`{.claim}.

- We have proved `A \/ B -> B \/ A`{.claim}.
  - Assume `A \/ B`{.hyp} (H). We prove `B \/ A` by case analysis on *H*{.just} (*or*{.just}, *match*{.just}):
    - Case 1: we prove `A -> B \/ A`{.claim}.
      - Assume `A`{.hyp} (H0). By definition of or (*or_intror*{.just}), from *H0*{.just} we deduce `B \/ A`{.claim}.
    - Case 2: we prove `B -> B \/ A`{.claim}.
      - Assume `B`{.hyp} (H0). By definition of or (*or_introl*{.just}), from *H0*{.just} we deduce `B \/ A`{.claim}.

    We have `B \/ A`{.claim} in all cases.
- We have proved `B \/ A -> A \/ B`{.claim}.
  - Assume `B \/ A`{.hyp} (H). We prove `A \/ B` by case analysis on *H*{.just} (*or*{.just}, *match*{.just}):
    - Case 1: we prove `B -> A \/ B`{.claim}.
      - Assume `B`{.hyp} (H0). By definition of or (*or_intror*{.just}), from *H0*{.just} we deduce `A \/ B`{.claim}.
    - Case 2: we prove `A -> A \/ B`{.claim}.
      - Assume `A`{.hyp} (H0). By definition of or (*or_introl*{.just}), from *H0*{.just} we deduce `A \/ B`{.claim}.

    We have `A \/ B`{.claim} in all cases.
- So by definition of and (*conj*{.just}), we have `(A \/ B -> B \/ A) /\ (B \/ A -> A \/ B)`{.claim}.
