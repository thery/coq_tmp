---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ Soit `E : Set`{.var}. Soit `R : Rel E`{.var}. Supposons `Trans E R`{.hyp} (h). Montrons `Trans E (Inv E R)`{.claim}.

- ▫️ Choisissons arbitrairement `x y z : E`{.var}; supposons `Inv E R x y`{.hyp} (h1) et `Inv E R y z`{.hyp} (h2).
  - ✅ Par h nous avons `Trans E R`{.claim}, c'est-à-dire `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
  - ▫️ L'élément `z`{.fact} appartient à `E`{.fact}.
  - ▫️ L'élément `y`{.fact} appartient à `E`{.fact}.
  - ▫️ L'élément `x`{.fact} appartient à `E`{.fact}.
  - ✅ Par h2 nous avons `Inv E R y z`{.claim}, c'est-à-dire `R z y`{.fact}.
  - ✅ Par h1 nous avons `Inv E R x y`{.claim}, c'est-à-dire `R y x`{.fact}.
  - ✅ Par application, nous avons `R z x`{.claim}, c'est-à-dire `Inv E R x z`{.fact}.
- ✅ Nous avons prouvé `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, c'est-à-dire `Trans E (Inv E R)`{.fact}.
