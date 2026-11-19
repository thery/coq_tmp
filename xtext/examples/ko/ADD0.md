---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ko
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

`m : nat`{.var} 라 하자. `m + 0 = m`{.claim} 임을 보이자.

- `m + 0 = m` 임을 보이자 *m*{.just} (*nat*{.just}, *induction*{.just}) 에 대한 귀납법으로:
  - 경우 1 (기저): `0 + 0 = 0 + 0`{.claim} 임을 보이자.
    - eq (*eq_refl*{.just}) 의 정의에 의해, `0 + 0 = 0 + 0`{.claim} 이다.
  - 경우 2 (귀납): `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim} 임을 보이자.
    - 임의로 택한 `m0 : nat`{.var}; 귀납 가정에 의해 `m0 + 0 = m0`{.hyp} (IH) 라고 가정하자.
      - 원소 `nat` 에 속한다 `Type`.
      - 원소 `nat` 에 속한다 `Type`.
      - 원소 `S` 에 속한다 `nat -> nat`.
      - 원소 `m0 + 0` 에 속한다 `nat`.
      - *IH*{.just} 에 의해 `m0 + 0 = m0`{.claim} 이다.

      적용하여 *f_equal*{.just}, `S (m0 + 0) = S m0`{.claim} 이다.

  이 경우들이 전부이므로, 따라서 `m + 0 = m`{.claim}.
