---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# nearly_reflexive

Let `A : Set`{.var}. Let `R : A -> A -> Prop`{.var}. Assume `forall x y : A, R x y -> R y x`{.hyp} (symmetry) and `forall x y z : A, R x y -> R y z -> R x z`{.hyp} (transitivity). Let `x : A`{.var}. Assume `exists y0 : A, R x y0`{.hyp} (h). We prove `R x x`{.claim}.

- Going back to the definition of ex (ex_ind) in `exists y0 : A, R x y0`{.fact} (h), we prove `R x x`{.claim}:
  - Let us consider an arbitrary `y0 : A`{.var}.
    - Assume `R x y0`{.hyp} (i).
      - By i we have `R x y0`{.claim}.
      - By i we have `R x y0`{.claim}.
      - By symmetry we have `forall x0 y : A, R x0 y -> R y x0`{.claim}.
      - By transitivity we have `forall x0 y z : A, R x0 y -> R y z -> R x0 z`{.claim}.
      - We deduce `R x x`{.claim} *by firstorder*.
