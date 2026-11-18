---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ko
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

`forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} 임을 보이자.

- `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} 임을 보이자 `l1`{.fact} (fix length_app') 에 대한 재귀로:
  - `A : Type`{.var} 라 하자.
  - `l1 l2 : list A`{.var} 라 하자.
  - `length (l1 ++ l2) = length l1 + length l2`{.fact} 임을 보이자 `l1`{.fact} (list, match) 에 대한 귀납법으로:
  - 경우 1 (기저): `length (nil ++ l2) = length (nil ++ l2)`{.claim} 임을 보이자.
    - eq (eq_refl) 의 정의에 의해, `length (nil ++ l2) = length (nil ++ l2)`{.claim} 이다 *by Corelib.Init.Logic.eq_refl*.
  - 경우 2 (귀납): `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim} 임을 보이자.
    - `x : A`{.var} 라 하자.
    - `l : list A`{.var} 라 하자.
    - 귀납 가정에 의해 (재귀 호출 length_app') `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim} 이다.
    - f_equal 을(를) 이용하여 `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} 임을 얻는다 *by Corelib.Init.Logic.f_equal*.
    - 따라서 `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - 이 경우들이 전부이므로, 따라서 `length (l1 ++ l2) = length l1 + length l2`{.claim}.
