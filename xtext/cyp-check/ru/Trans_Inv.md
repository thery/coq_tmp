---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Пусть `E : Set`{.var}. Пусть `R : Rel E`{.var}. Предположим, что `Trans E R`{.hyp} (h). Докажем, что `Trans E (Inv E R)`{.claim}.

- Выберем произвольно `x y z : E`{.var}; предположим, что `Inv E R x y`{.hyp} (h1) и `Inv E R y z`{.hyp} (h2).
  - По *h*{.just} имеем `Trans E R`, то есть `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
  - По *h2*{.just} имеем `Inv E R y z`, то есть `R z y`{.claim}.
  - По *h1*{.just} имеем `Inv E R x y`, то есть `R y x`{.claim}.

  Применением, имеем `R z x`, то есть `Inv E R x z`{.claim}.
- Мы доказали `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`, то есть `Trans E (Inv E R)`{.claim}.
