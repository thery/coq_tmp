---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ Soit `E : Set`{.var}. Soit `R : Rel E`{.var}. Supposons `Trans E R`{.hyp} (h). Montrons `Trans E (Inv E R)`{.claim}.

- ✅ Choisissons arbitrairement `x y z : E`{.var}; supposons `Inv E R x y`{.hyp} (h1) et `Inv E R y z`{.hyp} (h2).
  - ✅ Par *h*{.just} nous avons `Trans E R`, c'est-à-dire `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
  - ✅ Par *h2*{.just} nous avons `Inv E R y z`, c'est-à-dire `R z y`{.claim}.
  - ✅ Par *h1*{.just} nous avons `Inv E R x y`, c'est-à-dire `R y x`{.claim}.

  Par application, nous avons `R z x`, c'est-à-dire `Inv E R x z`{.claim}.
- ✅ Nous avons prouvé `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`, c'est-à-dire `Trans E (Inv E R)`{.claim}.
