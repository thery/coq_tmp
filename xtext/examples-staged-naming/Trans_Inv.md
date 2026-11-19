---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Let `E : Set`{.var}. Let `R : Rel E`{.var}. Assume `Trans E R`{.hyp} (h). We prove `Trans E (Inv E R)`{.claim}.

- Let us choose arbitrarily `x y z : E`{.var}; assume `Inv E R x y`{.hyp} (h1) and `Inv E R y z`{.hyp} (h2).
  - By *h*{.just} we have `Trans E R`, that is `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim} (P1).
  - By *h2*{.just} we have `Inv E R y z`, that is `R z y`{.claim} (P2).
  - By *h1*{.just} we have `Inv E R x y`, that is `R y x`{.claim} (P3).

  Applying *P1*{.just} to z, y, x, *P2*{.just} and *P3*{.just}, we have `R z x`, that is `Inv E R x z`{.claim}.
- We have proved `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`, that is `Trans E (Inv E R)`{.claim}.
