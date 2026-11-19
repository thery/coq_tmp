---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

ليكن `E : Set`{.var}. ليكن `R : Rel E`{.var}. لنفرض أن `Trans E R`{.hyp} (h). سنثبت أن `Trans E (Inv E R)`{.claim}.

- لنختر اختياريا `x y z : E`{.var}; لنفرض أن `Inv E R x y`{.hyp} (h1) و `Inv E R y z`{.hyp} (h2).
  - حسب *h*{.just} لدينا `Trans E R`, أي `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
  - حسب *h2*{.just} لدينا `Inv E R y z`, أي `R z y`{.claim}.
  - حسب *h1*{.just} لدينا `Inv E R x y`, أي `R y x`{.claim}.

  بالتطبيق, لدينا `R z x`, أي `Inv E R x z`{.claim}.
- لقد أثبتنا أن `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`, أي `Trans E (Inv E R)`{.claim}.
