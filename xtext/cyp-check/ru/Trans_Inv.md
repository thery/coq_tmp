---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Пусть `E : Set`{.var}. Пусть `R : Rel E`{.var}. Предположим, что `Trans E R`{.hyp} (h). Докажем, что `Trans E (Inv E R)`{.claim}.

- Выберем произвольно `x y z : E`{.var}; предположим, что `Inv E R x y`{.hyp} (h1) и `Inv E R y z`{.hyp} (h2).
  - По h имеем `Trans E R`{.claim}, то есть `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
  - Элемент `z`{.fact} принадлежит `E`{.fact}.
  - Элемент `y`{.fact} принадлежит `E`{.fact}.
  - Элемент `x`{.fact} принадлежит `E`{.fact}.
  - По h2 имеем `Inv E R y z`{.claim}, то есть `R z y`{.fact}.
  - По h1 имеем `Inv E R x y`{.claim}, то есть `R y x`{.fact}.
  - Применением, имеем `R z x`{.claim}, то есть `Inv E R x z`{.fact}.
- Мы доказали `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, то есть `Trans E (Inv E R)`{.fact}.
