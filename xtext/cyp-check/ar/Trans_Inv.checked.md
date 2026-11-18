---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ar
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ ليكن `E : Set`{.var}. ليكن `R : Rel E`{.var}. لنفرض أن `Trans E R`{.hyp} (h). لتكن `x y z : E`{.var}. لنفرض أن `Inv E R x y`{.hyp} (h1) و `Inv E R y z`{.hyp} (h2). سنثبت أن `Inv E R x z`{.claim}.

- ✅ حسب h2 لدينا `Inv E R y z`{.claim}, أي `R z y`{.fact}.
- ✅ حسب h1 لدينا `Inv E R x y`{.claim}, أي `R y x`{.fact}.
- ✅ حسب h لدينا `Trans E R`{.claim}, أي `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
- ✅ نستنتج أن `R z x`{.claim}, أي `Inv E R x z`{.fact}.
