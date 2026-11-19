---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ Sei `E : Set`{.var}. Sei `R : Rel E`{.var}. Angenommen `Trans E R`{.hyp} (h). Wir zeigen `Trans E (Inv E R)`{.claim}.

- ▫️ Seien beliebig `x y z : E`{.var}; angenommen `Inv E R x y`{.hyp} (h1) und `Inv E R y z`{.hyp} (h2).
  - ✅ Nach h es gilt `Trans E R`{.claim}, das heißt `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
  - ▫️ Das Element `z`{.fact} gehört zu `E`{.fact}.
  - ▫️ Das Element `y`{.fact} gehört zu `E`{.fact}.
  - ▫️ Das Element `x`{.fact} gehört zu `E`{.fact}.
  - ✅ Nach h2 es gilt `Inv E R y z`{.claim}, das heißt `R z y`{.fact}.
  - ✅ Nach h1 es gilt `Inv E R x y`{.claim}, das heißt `R y x`{.fact}.
  - ✅ Durch Anwendung, es gilt `R z x`{.claim}, das heißt `Inv E R x z`{.fact}.
- ✅ Wir haben gezeigt `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, das heißt `Trans E (Inv E R)`{.fact}.
