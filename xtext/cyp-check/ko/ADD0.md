---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ko
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

`m : nat`{.var} 라 하자. `m + 0 = m`{.claim} 임을 보이자.

- `m + 0 = m`{.fact} 귀납법으로 (nat, nat_ind) 을(를) 보이기 위해, `forall n : nat, n + 0 = n`{.fact} 로 일반화한다:
- 경우 1 (기저): `0 + 0 = 0 + 0`{.claim} 임을 보이자.
  - eq (eq_refl) 의 정의에 의해, `0 + 0 = 0 + 0`{.claim} 이다 *by Corelib.Init.Logic.eq_refl*.
- 경우 2 (귀납): `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim} 임을 보이자.
  - 임의의 `m0 : nat`{.var}.
    - 귀납 가정에 의해 `m0 + 0 = m0`{.hyp} (IH) 라고 가정하자.
      - IH 에 의해 `m0 + 0 = m0`{.claim} 이다.
      - f_equal 을(를) 이용하여 `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} 임을 얻는다 *by Corelib.Init.Logic.f_equal*.
      - 따라서 `S (m0 + 0) = S m0`{.claim}.
- 이 경우들이 전부이므로, 따라서 `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- 특히 `m + 0 = m`{.claim}.
