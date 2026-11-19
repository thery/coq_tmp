---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Let `E : Set`{.var}. Let `R : Rel E`{.var}. Assume `Trans E R`{.hyp} (h). Let `x y z : E`{.var}. Assume `Inv E R x y`{.hyp} (h1) and `Inv E R y z`{.hyp} (h2). We prove `Inv E R x z`{.claim}.

- By *h2*{.just} we have `Inv E R y z`, that is `R z y`{.claim}.
- By *h1*{.just} we have `Inv E R x y`, that is `R y x`{.claim}.
- By *h*{.just} we have `Trans E R`, that is `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
- We deduce `R z x`, that is `Inv E R x z`{.claim}.
