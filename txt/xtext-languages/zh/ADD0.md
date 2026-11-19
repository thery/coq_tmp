---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

设 `m : nat`{.var}. 我们证明 `m + 0 = m`{.claim}.

- 我们证明 `m + 0 = m` 用归纳法，对 `m` (nat, *nat_ind*{.just}):
  - 情形 1 (基础): 我们证明 `0 + 0 = 0 + 0`{.claim}.
    - 根据定义 eq (*eq_refl*{.just}), 我们有 `0 + 0 = 0 + 0`{.claim}.
  - 情形 2 (归纳): 我们证明 `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - 任意选取 `m0 : nat`{.var}; 假设 根据归纳假设 `m0 + 0 = m0`{.hyp} (IH).
      - 元素 `nat` 属于 `Type`.
      - 元素 `nat` 属于 `Type`.
      - 元素 `S` 属于 `nat -> nat`.
      - 元素 `m0 + 0` 属于 `nat`.
      - 根据 *IH*{.just} 我们有 `m0 + 0 = m0`{.claim}.

      将 *f_equal*{.just}, 我们有 `S (m0 + 0) = S m0`{.claim}.

  这些情形是穷尽的, 由此可得 `m + 0 = m`{.claim}.
