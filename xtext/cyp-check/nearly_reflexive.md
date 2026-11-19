---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# nearly_reflexive

Let `A : Set`{.var}. Let `R : A -> A -> Prop`{.var}. Assume `forall x y : A, R x y -> R y x`{.hyp} (symmetry) and `forall x y z : A, R x y -> R y z -> R x z`{.hyp} (transitivity). Let `x : A`{.var}. Assume `exists y0 : A, R x y0`{.hyp} (h). We prove `R x x`{.claim}.

- Going back to the definition of *ex*{.just} (*match*{.just}) in *h*{.just}, we prove `R x x`{.claim}:
  - Let us choose arbitrarily `y0 : A`{.var}; assume `R x y0`{.hyp} (i).
    - By *i*{.just} we have `R x y0`{.claim}.
    - Applying *symmetry*{.just} to x, y0 and *i*{.just}, we have `R y0 x`{.claim}.

    Applying *transitivity*{.just}, we have `R x x`{.claim}.
