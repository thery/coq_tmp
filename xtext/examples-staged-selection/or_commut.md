---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (h). We prove `B \/ A`{.claim}.

- We prove `B \/ A` by case analysis on *h*{.just} (*or*{.just}, *match*{.just}):
  - Case 1: we prove `A -> B \/ A`{.claim}.
    - Assume `A`{.hyp} (i). By definition of or (*or_intror*{.just}), from *i*{.just} we deduce `B \/ A`{.claim}.
  - Case 2: we prove `B -> B \/ A`{.claim}.
    - Assume `B`{.hyp} (j). By definition of or (*or_introl*{.just}), from *j*{.just} we deduce `B \/ A`{.claim}.

  We have `B \/ A`{.claim} in all cases.
