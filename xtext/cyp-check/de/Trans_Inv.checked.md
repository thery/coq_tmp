---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: de
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ Sei `E : Set`{.var}. Sei `R : Rel E`{.var}. Angenommen `Trans E R`{.hyp} (h). Wir zeigen `Trans E (Inv E R)`{.claim}.

- ✅ Seien beliebig `x y z : E`{.var}; angenommen `Inv E R x y`{.hyp} (h1) und `Inv E R y z`{.hyp} (h2).
  - ✅ Nach *h*{.just} es gilt `Trans E R`, das heißt `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
  - ✅ Nach *h2*{.just} es gilt `Inv E R y z`, das heißt `R z y`{.claim}.
  - ✅ Nach *h1*{.just} es gilt `Inv E R x y`, das heißt `R y x`{.claim}.

  Durch Anwendung, es gilt `R z x`, das heißt `Inv E R x z`{.claim}.
- ✅ Wir haben gezeigt `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`, das heißt `Trans E (Inv E R)`{.claim}.
