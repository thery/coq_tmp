---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: zh
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

我们证明 `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- 我们证明 `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} 用递归，对 `l1` (fix length_app'):
  - 设 `A : Type`{.var} 且 `l1 l2 : list A`{.var}. 我们证明 `length (l1 ++ l2) = length l1 + length l2` 用归纳法，对 *l1*{.just} (*list*{.just}, *induction*{.just}):
    - 情形 1 (基础): 我们证明 `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - 根据定义 eq (*eq_refl*{.just}), 我们有 `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - 情形 2 (归纳): 我们证明 `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - 设 `x : A`{.var} 且 `l : list A`{.var}.
        - 元素 `nat` 属于 `Type`.
        - 元素 `nat` 属于 `Type`.
        - 元素 `S` 属于 `nat -> nat`.
        - 元素 `length (l ++ l2)` 属于 `nat`.
        - 元素 `length l + length l2` 属于 `nat`.
        - 特别地 `length (l ++ l2) = length l + length l2`{.claim}.
          - 根据归纳假设 (递归调用 length_app') 我们有 `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.

        将 *f_equal*{.just}, 我们有 `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.

    这些情形是穷尽的, 由此可得 `length (l1 ++ l2) = length l1 + length l2`{.claim}.
