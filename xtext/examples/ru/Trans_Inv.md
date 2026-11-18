---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Пусть `E : Set`{.var}. Пусть `R : Rel E`{.var}. Предположим, что `Trans E R`{.hyp} (h). Пусть `x y z : E`{.var}. Предположим, что `Inv E R x y`{.hyp} (h1) и `Inv E R y z`{.hyp} (h2). Докажем, что `Inv E R x z`{.claim}.

- По h2 имеем `Inv E R y z`{.claim}, то есть `R z y`{.fact}.
- По h1 имеем `Inv E R x y`{.claim}, то есть `R y x`{.fact}.
- По h имеем `Trans E R`{.claim}, то есть `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
- Следовательно `R z x`{.claim}, то есть `Inv E R x z`{.fact}.
