---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Let `E : Set`{.var}. Let `R : Rel E`{.var}. Assume `Trans E R`{.hyp} (h). We prove `Trans E (Inv E R)`{.claim}.

- Let us choose arbitrarily `x y z : E`{.var}; assume `Inv E R x y`{.hyp} (h1) and `Inv E R y z`{.hyp} (h2).
  - By h we have `Trans E R`{.claim}, that is `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
  - The element `z`{.fact} belongs to `E`{.fact}.
  - The element `y`{.fact} belongs to `E`{.fact}.
  - The element `x`{.fact} belongs to `E`{.fact}.
  - By h2 we have `Inv E R y z`{.claim}, that is `R z y`{.fact}.
  - By h1 we have `Inv E R x y`{.claim}, that is `R y x`{.fact}.
  - By application, we have `R z x`{.claim}, that is `Inv E R x z`{.fact}.
- We have proved `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, that is `Trans E (Inv E R)`{.fact}.
