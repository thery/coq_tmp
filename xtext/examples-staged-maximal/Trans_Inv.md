---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Let `E : Set`{.var}. Let `R : Rel E`{.var}. Assume `Trans E R`{.hyp} (h). We prove `Trans E (Inv E R)`{.claim}.

- Let us choose arbitrarily `x y z : E`{.var}; assume `Inv E R x y`{.hyp} (h1) and `Inv E R y z`{.hyp} (h2).
  - Applying h to z, y, x, h2 and h1, we have `R z x`{.claim}, that is `Inv E R x z`{.fact}.
- We have proved `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, that is `Trans E (Inv E R)`{.fact}.
