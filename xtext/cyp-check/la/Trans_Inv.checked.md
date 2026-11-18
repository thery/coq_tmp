---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ Sit `E : Set`{.var}. Sit `R : Rel E`{.var}. Ponamus `Trans E R`{.hyp} (h). Sint `x y z : E`{.var}. Ponamus `Inv E R x y`{.hyp} (h1) et `Inv E R y z`{.hyp} (h2). Ostendamus `Inv E R x z`{.claim}.

- ✅ Per h2 habemus `Inv E R y z`{.claim}, id est `R z y`{.fact}.
- ✅ Per h1 habemus `Inv E R x y`{.claim}, id est `R y x`{.fact}.
- ✅ Per h habemus `Trans E R`{.claim}, id est `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
- ✅ Unde sequitur `R z x`{.claim}, id est `Inv E R x z`{.fact}.
