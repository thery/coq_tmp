---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: zh
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

设 `E : Set`{.var}. 设 `R : Rel E`{.var}. 假设 `Trans E R`{.hyp} (h). 设 `x y z : E`{.var}. 假设 `Inv E R x y`{.hyp} (h1) 且 `Inv E R y z`{.hyp} (h2). 我们证明 `Inv E R x z`{.claim}.

- 根据 h2 我们有 `Inv E R y z`{.claim}, 即 `R z y`{.fact}.
- 根据 h1 我们有 `Inv E R x y`{.claim}, 即 `R y x`{.fact}.
- 根据 h 我们有 `Trans E R`{.claim}, 即 `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
- 由此可得 `R z x`{.claim}, 即 `Inv E R x z`{.fact}.
