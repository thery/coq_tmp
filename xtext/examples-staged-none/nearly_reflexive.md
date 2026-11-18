---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# nearly_reflexive

Let `A : Set`{.var}. Let `R : A -> A -> Prop`{.var}. Assume `forall x y : A, R x y -> R y x`{.hyp} (symmetry) and `forall x y z : A, R x y -> R y z -> R x z`{.hyp} (transitivity). Let `x : A`{.var}. Assume `exists y0 : A, R x y0`{.hyp} (h). We prove `R x x`{.claim}.

- Going back to the definition of ex (ex_ind) in `exists y0 : A, R x y0`{.fact} (h), we prove `R x x`{.claim}:
  - Let us choose arbitrarily `y0 : A`{.var}.
    - Assume `R x y0`{.hyp} (i).
      - By application, we have `R y0 x -> R x x`{.claim}.
        - By application, we have `R x y0 -> R y0 x -> R x x`{.claim}.
          - By application, we have `forall z : A, R x y0 -> R y0 z -> R x z`{.claim}.
            - By application, we have `forall y z : A, R x y -> R y z -> R x z`{.claim}.
              - By transitivity we have `forall elpi_ctx_entry_8_ y z : A, R elpi_ctx_entry_8_ y -> R y z -> R elpi_ctx_entry_8_ z`{.claim}.
              - The element `x`{.fact} belongs to `A`{.fact}.
            - The element `y0`{.fact} belongs to `A`{.fact}.
          - The element `x`{.fact} belongs to `A`{.fact}.
        - By i we have `R x y0`{.claim}.
      - By application, we have `R y0 x`{.claim}.
        - By application, we have `R x y0 -> R y0 x`{.claim}.
          - By application, we have `forall y : A, R x y -> R y x`{.claim}.
            - By symmetry we have `forall elpi_ctx_entry_8_ y : A, R elpi_ctx_entry_8_ y -> R y elpi_ctx_entry_8_`{.claim}.
            - The element `x`{.fact} belongs to `A`{.fact}.
          - The element `y0`{.fact} belongs to `A`{.fact}.
        - By i we have `R x y0`{.claim}.
      - By application, we have `R x x`{.claim}.
