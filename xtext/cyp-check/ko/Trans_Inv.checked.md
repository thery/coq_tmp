---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ko
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ `E : Set`{.var} 라 하자. `R : Rel E`{.var} 라 하자. `Trans E R`{.hyp} (h) 라고 가정하자. `x y z : E`{.var} 라 하자. `Inv E R x y`{.hyp} (h1) 그리고 `Inv E R y z`{.hyp} (h2) 라고 가정하자. `Inv E R x z`{.claim} 임을 보이자.

- ✅ h2 에 의해 `Inv E R y z`{.claim} 이다, 즉 `R z y`{.fact}.
- ✅ h1 에 의해 `Inv E R x y`{.claim} 이다, 즉 `R y x`{.fact}.
- ✅ h 에 의해 `Trans E R`{.claim} 이다, 즉 `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
- ✅ 따라서 `R z x`{.claim}, 즉 `Inv E R x z`{.fact}.
