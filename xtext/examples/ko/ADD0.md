---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ko
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

`m : nat`{.var} 라 하자. `m + 0 = m`{.claim} 임을 보이자.

- `m + 0 = m`{.fact} 귀납법으로 (nat, nat_ind) 을(를) 보이기 위해, `forall n : nat, n + 0 = n`{.fact} 로 일반화한다:
- 경우 1 (기저): `0 + 0 = 0 + 0`{.claim} 임을 보이자.
  - eq (eq_refl) 의 정의에 의해, `0 + 0 = 0 + 0`{.claim} 이다 *by Corelib.Init.Logic.eq_refl*.
- 경우 2 (귀납): `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim} 임을 보이자.
  - 임의로 택한 `m0 : nat`{.var}; 귀납 가정에 의해 `m0 + 0 = m0`{.hyp} (IH) 라고 가정하자.
    - 원소 `nat`{.fact} 에 속한다 `Type`{.fact}.
    - 원소 `nat`{.fact} 에 속한다 `Type`{.fact}.
    - 원소 `S`{.fact} 에 속한다 `nat -> nat`{.fact}.
    - 원소 `m0 + 0`{.fact} 에 속한다 `nat`{.fact}.
    - 원소 `m0`{.fact} 에 속한다 `nat`{.fact}.
    - IH 에 의해 `m0 + 0 = m0`{.claim} 이다.
    - 적용하여 f_equal, `S (m0 + 0) = S m0`{.claim} 이다.
- 이 경우들이 전부이므로, 따라서 `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- 특히 `m + 0 = m`{.claim}.
