---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Sit `E : Set`{.var}. Sit `R : Rel E`{.var}. Ponamus `Trans E R`{.hyp} (h). Ostendamus `Trans E (Inv E R)`{.claim}.

- Eligamus quaelibet `x y z : E`{.var}; ponamus `Inv E R x y`{.hyp} (h1) et `Inv E R y z`{.hyp} (h2).
  - Per *h*{.just} habemus `Trans E R`, id est `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
  - Per *h2*{.just} habemus `Inv E R y z`, id est `R z y`{.claim}.
  - Per *h1*{.just} habemus `Inv E R x y`, id est `R y x`{.claim}.

  Per applicationem, habemus `R z x`, id est `Inv E R x z`{.claim}.
- Ostendimus `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`, id est `Trans E (Inv E R)`{.claim}.
