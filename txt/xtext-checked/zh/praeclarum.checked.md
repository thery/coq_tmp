---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

✅ 设 `x y z t : Prop`{.var}. 假设 `(x -> z) /\ (y -> t)`{.hyp} (h1) 且 `x /\ y`{.hyp} (h2). 我们证明 `z /\ t`{.claim}.

- ✅ 回到定义 and (*and_ind*{.just}) 于 *h1*{.just}, 我们证明 `z /\ t`{.claim}:
  - ✅ 假设 `x -> z`{.hyp} (i) 且 `y -> t`{.hyp} (j). 回到定义 and (*and_ind*{.just}) 于 *h2*{.just}, 我们证明 `z /\ t`{.claim}:
    - ✅ 假设 `x`{.hyp} (k) 且 `y`{.hyp} (l).
      - ✅ 将 *i*{.just} 应用于 *k*{.just}, 我们有 `z`{.claim}.
      - ✅ 将 *j*{.just} 应用于 *l*{.just}, 我们有 `t`{.claim}.

      所以 根据定义 and (*conj*{.just}), 我们有 `z /\ t`{.claim}.
