---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ko
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ `E : Set`{.var} 라 하자. `R : Rel E`{.var} 라 하자. `Trans E R`{.hyp} (h) 라고 가정하자. `Trans E (Inv E R)`{.claim} 임을 보이자.

- ✅ 임의로 택한 `x y z : E`{.var}; `Inv E R x y`{.hyp} (h1) 그리고 `Inv E R y z`{.hyp} (h2) 라고 가정하자.
  - ✅ *h*{.just} 에 의해 `Trans E R` 이다, 즉 `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
  - ✅ *h2*{.just} 에 의해 `Inv E R y z` 이다, 즉 `R z y`{.claim}.
  - ✅ *h1*{.just} 에 의해 `Inv E R x y` 이다, 즉 `R y x`{.claim}.

  적용에 의해, `R z x` 이다, 즉 `Inv E R x z`{.claim}.
- ✅ `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0` 임을 보였다, 즉 `Trans E (Inv E R)`{.claim}.
