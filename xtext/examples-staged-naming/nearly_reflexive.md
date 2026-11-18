---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# nearly_reflexive

Let `A : Set`{.var}. Let `R : A -> A -> Prop`{.var}. Assume `forall x y : A, R x y -> R y x`{.hyp} (symmetry) and `forall x y z : A, R x y -> R y z -> R x z`{.hyp} (transitivity). Let `x : A`{.var}. Assume `exists y0 : A, R x y0`{.hyp} (h). We prove `R x x`{.claim}.

- Going back to the definition of ex (ex_ind) in `exists y0 : A, R x y0`{.fact} (h), we prove `R x x`{.claim}:
  - Let us choose arbitrarily `y0 : A`{.var}; assume `R x y0`{.hyp} (i).
    - Applying symmetry to x, y0 and i, we have `R y0 x`{.claim} (P1).
    - Applying transitivity to x, y0, x, i and P1, we have `R x x`{.claim}.
