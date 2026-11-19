---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

设 `n m : nat`{.var}. 我们证明 `S (n + m) = n + S m`{.claim}.

- 我们证明 `S (n + m) = n + S m` 用归纳法，对 *n*{.just} (*nat*{.just}, *induction*{.just}):
  - 情形 1 (基础): 我们证明 `0 + S m = 0 + S m`{.claim}.
    - 根据定义 eq (*eq_refl*{.just}), 我们有 `0 + S m = 0 + S m`{.claim}.
  - 情形 2 (归纳): 我们证明 `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
    - 任意选取 `n0 : nat`{.var}; 假设 根据归纳假设 `S (n0 + m) = n0 + S m`{.hyp} (IH).
      - 根据定义 eq (*eq_refl*{.just}), 我们有 `S (n0 + S m) = S (n0 + S m)`{.claim}.
      - 根据 *IH*{.just} 我们有 `S (n0 + m) = n0 + S m`{.claim}.

      用等式改写 `S (n0 + m) = n0 + S m`{.fact} 从右到左 (eq_ind_r), 我们得到 `S (S (n0 + m)) = S (n0 + S m)`{.claim}.

  这些情形是穷尽的, 由此可得 `S (n + m) = n + S m`{.claim}.
