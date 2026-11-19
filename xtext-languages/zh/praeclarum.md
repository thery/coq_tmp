---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

设 `x y z t : Prop`{.var}. 假设 `(x -> z) /\ (y -> t)`{.hyp} (h1) 且 `x /\ y`{.hyp} (h2). 我们证明 `z /\ t`{.claim}.

- 回到定义 and (and_ind) 于 `(x -> z) /\ (y -> t)`{.fact} (h1), 我们证明 `z /\ t`{.claim}:
  - 假设 `x -> z`{.hyp} (i) 且 `y -> t`{.hyp} (j).
    - 回到定义 and (and_ind) 于 `x /\ y`{.fact} (h2), 我们证明 `z /\ t`{.claim}:
      - 假设 `x`{.hyp} (k) 且 `y`{.hyp} (l).
        - 将 i 应用于 k, 我们有 `z`{.claim}.
        - 将 j 应用于 l, 我们有 `t`{.claim}.
        - 所以 根据定义 and (conj), 我们有 `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
