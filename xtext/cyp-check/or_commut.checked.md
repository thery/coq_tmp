---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

✅ Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (h). We prove `B \/ A`{.claim}.

- ▫️ We prove `B \/ A`{.fact} by case analysis on `A \/ B`{.fact} (h) (or, or_ind):
- ✅ Case 1: we prove `A -> B \/ A`{.claim}.
  - ▫️ Assume `A`{.hyp} (i).
    - ✅ By definition of or (or_intror), from `A`{.fact} (i) we deduce `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- ✅ Case 2: we prove `B -> B \/ A`{.claim}.
  - ▫️ Assume `B`{.hyp} (j).
    - ✅ By definition of or (or_introl), from `B`{.fact} (j) we deduce `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- ✅ We have `B \/ A`{.claim} in all cases.
