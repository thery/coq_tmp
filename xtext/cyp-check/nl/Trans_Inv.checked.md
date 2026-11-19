---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: nl
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ Laat `E : Set`{.var}. Laat `R : Rel E`{.var}. Stel `Trans E R`{.hyp} (h). We bewijzen `Trans E (Inv E R)`{.claim}.

- ▫️ Kies willekeurig `x y z : E`{.var}; stel `Inv E R x y`{.hyp} (h1) en `Inv E R y z`{.hyp} (h2).
  - ✅ Volgens h er geldt `Trans E R`{.claim}, dat wil zeggen `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
  - ▫️ Het element `z`{.fact} behoort tot `E`{.fact}.
  - ▫️ Het element `y`{.fact} behoort tot `E`{.fact}.
  - ▫️ Het element `x`{.fact} behoort tot `E`{.fact}.
  - ✅ Volgens h2 er geldt `Inv E R y z`{.claim}, dat wil zeggen `R z y`{.fact}.
  - ✅ Volgens h1 er geldt `Inv E R x y`{.claim}, dat wil zeggen `R y x`{.fact}.
  - ✅ Door toepassing, er geldt `R z x`{.claim}, dat wil zeggen `Inv E R x z`{.fact}.
- ✅ We hebben bewezen `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, dat wil zeggen `Trans E (Inv E R)`{.fact}.
