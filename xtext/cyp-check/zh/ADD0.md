---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: zh
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

设 `m : nat`{.var}. 我们证明 `m + 0 = m`{.claim}.

- 我们证明 `m + 0 = m`{.fact} 用归纳法，对 `m`{.fact} (nat, nat_ind):
- 情形 1 (基础): 我们证明 `0 + 0 = 0 + 0`{.claim}.
  - 根据定义 eq (eq_refl), 我们有 `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- 情形 2 (归纳): 我们证明 `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - 任意选取 `m0 : nat`{.var}; 假设 根据归纳假设 `m0 + 0 = m0`{.hyp} (IH).
    - 元素 `nat`{.fact} 属于 `Type`{.fact}.
    - 元素 `nat`{.fact} 属于 `Type`{.fact}.
    - 元素 `S`{.fact} 属于 `nat -> nat`{.fact}.
    - 元素 `m0 + 0`{.fact} 属于 `nat`{.fact}.
    - 元素 `m0`{.fact} 属于 `nat`{.fact}.
    - 根据 IH 我们有 `m0 + 0 = m0`{.claim}.
    - 将 f_equal, 我们有 `S (m0 + 0) = S m0`{.claim}.
- 这些情形是穷尽的, 由此可得 `m + 0 = m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
