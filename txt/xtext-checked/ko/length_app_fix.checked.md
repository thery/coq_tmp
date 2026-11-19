---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ko
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

✅ `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} 임을 보이자.

- ✅ `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} 임을 보이자 `l1` (fix length_app') 에 대한 재귀로:
  - ✅ `A : Type`{.var} 그리고 `l1 l2 : list A`{.var} 라 하자. `length (l1 ++ l2) = length l1 + length l2` 임을 보이자 *l1*{.just} (*list*{.just}, *induction*{.just}) 에 대한 귀납법으로:
    - ✅ 경우 1 (기저): `length (nil ++ l2) = length (nil ++ l2)`{.claim} 임을 보이자.
      - ✅ eq (*eq_refl*{.just}) 의 정의에 의해, `length (nil ++ l2) = length (nil ++ l2)`{.claim} 이다.
    - ✅ 경우 2 (귀납): `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim} 임을 보이자.
      - ✅ `x : A`{.var} 그리고 `l : list A`{.var} 라 하자.
        - ▫️ 원소 `nat` 에 속한다 `Type`.
        - ▫️ 원소 `nat` 에 속한다 `Type`.
        - ▫️ 원소 `S` 에 속한다 `nat -> nat`.
        - ▫️ 원소 `length (l ++ l2)` 에 속한다 `nat`.
        - ▫️ 원소 `length l + length l2` 에 속한다 `nat`.
        - ✅ 특히 `length (l ++ l2) = length l + length l2`{.claim}.
          - ✅ 귀납 가정에 의해 (재귀 호출 length_app') `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim} 이다.

        적용하여 *f_equal*{.just}, `S (length (l ++ l2)) = S (length l + length l2)`{.claim} 이다.

    이 경우들이 전부이므로, 따라서 `length (l1 ++ l2) = length l1 + length l2`{.claim}.
