---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: zh
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

我们证明 `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- 我们证明 `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} 用递归，对 `l1`{.fact} (fix length_app'):
  - 设 `A : Type`{.var}.
  - 设 `l1 l2 : list A`{.var}.
  - 我们证明 `length (l1 ++ l2) = length l1 + length l2`{.fact} 用归纳法，对 `l1`{.fact} (list, match):
  - 情形 1 (基础): 我们证明 `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - 根据定义 eq (eq_refl), 我们有 `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - 情形 2 (归纳): 我们证明 `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - 设 `x : A`{.var}.
    - 设 `l : list A`{.var}.
    - 根据归纳假设 (递归调用 length_app') 我们有 `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
    - 利用 f_equal 我们得到 `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
    - 由此可得 `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - 这些情形是穷尽的, 由此可得 `length (l1 ++ l2) = length l1 + length l2`{.claim}.
