---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Sei `E : Set`{.var}. Sei `R : Rel E`{.var}. Angenommen `Trans E R`{.hyp} (h). Seien `x y z : E`{.var}. Angenommen `Inv E R x y`{.hyp} (h1) und `Inv E R y z`{.hyp} (h2). Wir zeigen `Inv E R x z`{.claim}.

- Nach h2 es gilt `Inv E R y z`{.claim}, das heißt `R z y`{.fact}.
- Nach h1 es gilt `Inv E R x y`{.claim}, das heißt `R y x`{.fact}.
- Nach h es gilt `Trans E R`{.claim}, das heißt `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
- Daraus folgt `R z x`{.claim}, das heißt `Inv E R x z`{.fact}.
