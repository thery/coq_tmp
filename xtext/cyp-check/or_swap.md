---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_swap

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (H). We prove `B \/ A`{.claim}.

- We prove `B \/ A` by case analysis on *H*{.just} (or, match):
  - Case 1: we prove `A -> B \/ A`{.claim}.
    - Assume `A`{.hyp} (a). By definition of or (*or_intror*{.just}), from *a*{.just} we deduce `B \/ A`{.claim}.
  - Case 2: we prove `B -> B \/ A`{.claim}.
    - Assume `B`{.hyp} (b). By definition of or (*or_introl*{.just}), from *b*{.just} we deduce `B \/ A`{.claim}.

  We have `B \/ A`{.claim} in all cases.
