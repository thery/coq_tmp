---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Sia `E : Set`{.var}. Sia `R : Rel E`{.var}. Supponiamo `Trans E R`{.hyp} (h). Siano `x y z : E`{.var}. Supponiamo `Inv E R x y`{.hyp} (h1) e `Inv E R y z`{.hyp} (h2). Dimostriamo `Inv E R x z`{.claim}.

- Per h2 abbiamo `Inv E R y z`{.claim}, cioè `R z y`{.fact}.
- Per h1 abbiamo `Inv E R x y`{.claim}, cioè `R y x`{.fact}.
- Per h abbiamo `Trans E R`{.claim}, cioè `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
- Ne deduciamo `R z x`{.claim}, cioè `Inv E R x z`{.fact}.
