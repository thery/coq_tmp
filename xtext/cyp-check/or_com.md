---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_com

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (H). We prove `B \/ A`{.claim}.

- We prove `B \/ A` by case analysis on *H*{.just} (or, *or_ind*{.just}):
  - Case 1: we prove `A -> B \/ A`{.claim}.
    - Assume `A`{.hyp} (H0). By definition of or (*or_intror*{.just}), from *H0*{.just} we deduce `B \/ A`{.claim}.
  - Case 2: we prove `B -> B \/ A`{.claim}.
    - Assume `B`{.hyp} (H0). By definition of or (*or_introl*{.just}), from *H0*{.just} we deduce `B \/ A`{.claim}.

  We have `B \/ A`{.claim} in all cases.
