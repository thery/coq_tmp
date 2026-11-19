---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ 设 `n m : nat`{.var}. 假设 `n <= m`{.hyp} (H). 我们证明 `S n <= S m`{.claim}.

- ▫️ 我们证明 `S n <= S m`{.fact} 用归纳法，对 `n <= m`{.fact} (H) (le, le_ind):
- ✅ 情形 1 (基础): 我们证明 `S n <= S n`{.claim}.
  - ✅ 根据定义 le (le_n), 我们有 `S n <= S n`{.claim} *by Corelib.Init.Peano.le_n*.
- ✅ 情形 2 (归纳): 我们证明 `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - ▫️ 任意选取 `m0 : nat`{.var}; 假设 `n <= m0`{.hyp} (H0) 且 根据归纳假设 `S n <= S m0`{.hyp} (IH).
    - ✅ 根据定义 le (le_S) 取见证 `S m0`{.fact}, 由 `S n <= S m0`{.fact} (IH) 由此可得 `S n <= S (S m0)`{.claim} *by Corelib.Init.Peano.le_S*.
- ✅ 我们有 `S n <= S m`{.claim} 在所有情形下.
