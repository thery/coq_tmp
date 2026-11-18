---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Laat `E : Set`{.var}. Laat `R : Rel E`{.var}. Stel `Trans E R`{.hyp} (h). Laat `x y z : E`{.var}. Stel `Inv E R x y`{.hyp} (h1) en `Inv E R y z`{.hyp} (h2). We bewijzen `Inv E R x z`{.claim}.

- Volgens h2 er geldt `Inv E R y z`{.claim}, dat wil zeggen `R z y`{.fact}.
- Volgens h1 er geldt `Inv E R x y`{.claim}, dat wil zeggen `R y x`{.fact}.
- Volgens h er geldt `Trans E R`{.claim}, dat wil zeggen `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
- Hieruit volgt `R z x`{.claim}, dat wil zeggen `Inv E R x z`{.fact}.
