---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ar
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ ليكن `E : Set`{.var}. ليكن `R : Rel E`{.var}. لنفرض أن `Trans E R`{.hyp} (h). سنثبت أن `Trans E (Inv E R)`{.claim}.

- ▫️ لنختر اختياريا `x y z : E`{.var}; لنفرض أن `Inv E R x y`{.hyp} (h1) و `Inv E R y z`{.hyp} (h2).
  - ✅ حسب h لدينا `Trans E R`{.claim}, أي `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
  - ▫️ العنصر `z`{.fact} ينتمي إلى `E`{.fact}.
  - ▫️ العنصر `y`{.fact} ينتمي إلى `E`{.fact}.
  - ▫️ العنصر `x`{.fact} ينتمي إلى `E`{.fact}.
  - ✅ حسب h2 لدينا `Inv E R y z`{.claim}, أي `R z y`{.fact}.
  - ✅ حسب h1 لدينا `Inv E R x y`{.claim}, أي `R y x`{.fact}.
  - ✅ بالتطبيق, لدينا `R z x`{.claim}, أي `Inv E R x z`{.fact}.
- ✅ لقد أثبتنا أن `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, أي `Trans E (Inv E R)`{.fact}.
