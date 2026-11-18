---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: zh
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

设 `m : nat`{.var}. 我们证明 `m + 0 = m`{.claim}.

- 为证明 `m + 0 = m`{.fact} 用归纳法 (nat, nat_ind), 我们将其推广为 `forall n : nat, n + 0 = n`{.fact}:
- 情形 1 (基础): 我们证明 `0 + 0 = 0 + 0`{.claim}.
  - 根据定义 eq (eq_refl), 我们有 `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- 情形 2 (归纳): 我们证明 `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - 任取 `m0 : nat`{.var}.
    - 假设 根据归纳假设 `m0 + 0 = m0`{.hyp} (IH).
      - 根据 IH 我们有 `m0 + 0 = m0`{.claim}.
      - 利用 f_equal 我们得到 `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
      - 由此可得 `S (m0 + 0) = S m0`{.claim}.
- 这些情形是穷尽的, 由此可得 `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- 特别地 `m + 0 = m`{.claim}.
