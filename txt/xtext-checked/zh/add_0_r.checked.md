---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

✅ 设 `n : nat`{.var}. 我们证明 `n + 0 = n`{.claim}.

- ▫️ 我们证明 `n + 0 = n`{.fact} 用归纳法，对 `n`{.fact} (nat, nat_ind):
- ✅ 情形 1 (基础): 我们证明 `0 = 0`{.claim}.
  - ✅ 根据定义 eq (eq_refl), 我们有 `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ 情形 2 (归纳): 我们证明 `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - ▫️ 任意选取 `m : nat`{.var}; 假设 根据归纳假设 `m + 0 = m`{.hyp} (IH).
    - ✅ 根据定义 eq (eq_refl), 我们有 `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - ✅ 根据 IH 我们有 `m + 0 = m`{.claim}.
    - ✅ 用等式改写 `m + 0 = m`{.fact} 从右到左 (eq_ind_r), 我们得到 `S (m + 0) = S m`{.claim}.
- ✅ 这些情形是穷尽的, 由此可得 `n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
