---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

✅ 设 `E : Set`{.var}. 设 `R : Rel E`{.var}. 假设 `Trans E R`{.hyp} (h). 我们证明 `Trans E (Inv E R)`{.claim}.

- ✅ 任意选取 `x y z : E`{.var}; 假设 `Inv E R x y`{.hyp} (h1) 且 `Inv E R y z`{.hyp} (h2).
  - ✅ 根据 *h*{.just} 我们有 `Trans E R`, 即 `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
  - ✅ 根据 *h2*{.just} 我们有 `Inv E R y z`, 即 `R z y`{.claim}.
  - ✅ 根据 *h1*{.just} 我们有 `Inv E R x y`, 即 `R y x`{.claim}.

  由应用, 我们有 `R z x`, 即 `Inv E R x z`{.claim}.
- ✅ 我们已证明 `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`, 即 `Trans E (Inv E R)`{.claim}.
