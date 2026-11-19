---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ Sit `E : Set`{.var}. Sit `R : Rel E`{.var}. Ponamus `Trans E R`{.hyp} (h). Ostendamus `Trans E (Inv E R)`{.claim}.

- ▫️ Eligamus quaelibet `x y z : E`{.var}; ponamus `Inv E R x y`{.hyp} (h1) et `Inv E R y z`{.hyp} (h2).
  - ✅ Per h habemus `Trans E R`{.claim}, id est `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
  - ▫️ Elementum `z`{.fact} pertinet ad `E`{.fact}.
  - ▫️ Elementum `y`{.fact} pertinet ad `E`{.fact}.
  - ▫️ Elementum `x`{.fact} pertinet ad `E`{.fact}.
  - ✅ Per h2 habemus `Inv E R y z`{.claim}, id est `R z y`{.fact}.
  - ✅ Per h1 habemus `Inv E R x y`{.claim}, id est `R y x`{.fact}.
  - ✅ Per applicationem, habemus `R z x`{.claim}, id est `Inv E R x z`{.fact}.
- ✅ Ostendimus `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, id est `Trans E (Inv E R)`{.fact}.
