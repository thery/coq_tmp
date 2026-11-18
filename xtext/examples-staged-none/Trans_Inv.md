---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Let `E : Set`{.var}. Let `R : Rel E`{.var}. Assume `Trans E R`{.hyp} (h). We prove `Trans E (Inv E R)`{.claim}.

- Let us choose arbitrarily `x : E`{.var}.
  - Let us choose arbitrarily `y : E`{.var}.
    - Let us choose arbitrarily `z : E`{.var}.
      - Assume `Inv E R x y`{.hyp} (h1).
        - Assume `Inv E R y z`{.hyp} (h2).
          - By application, we have `R y x -> R z x`{.claim}.
            - By application, we have `R z y -> R y x -> R z x`{.claim}.
              - By application, we have `forall z0 : E, R z y -> R y z0 -> R z z0`{.claim}.
                - By application, we have `forall y0 z0 : E, R z y0 -> R y0 z0 -> R z z0`{.claim}.
                  - By h we have `Trans E R`{.claim}, that is `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
                  - The element `z`{.fact} belongs to `E`{.fact}.
                - The element `y`{.fact} belongs to `E`{.fact}.
              - The element `x`{.fact} belongs to `E`{.fact}.
            - By h2 we have `Inv E R y z`{.claim}, that is `R z y`{.fact}.
          - By h1 we have `Inv E R x y`{.claim}, that is `R y x`{.fact}.
          - By application, we have `R z x`{.claim}, that is `Inv E R x z`{.fact}.
        - We have proved `Inv E R y z -> Inv E R x z`{.claim}.
      - We have proved `Inv E R x y -> Inv E R y z -> Inv E R x z`{.claim}.
    - We have proved `forall z0 : E, Inv E R x y -> Inv E R y z0 -> Inv E R x z0`{.claim}.
  - We have proved `forall y0 z : E, Inv E R x y0 -> Inv E R y0 z -> Inv E R x z`{.claim}.
- We have proved `forall x0 y z : E, Inv E R x0 y -> Inv E R y z -> Inv E R x0 z`{.claim}, that is `Trans E (Inv E R)`{.fact}.
