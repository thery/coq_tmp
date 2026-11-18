---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ko
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

`n m : nat`{.var} 라 하자. `S (n + m) = n + S m`{.claim} 임을 보이자.

- `S (n + m) = n + S m`{.fact} 귀납법으로 (nat, nat_ind) 을(를) 보이기 위해, `forall n0 : nat, S (n0 + m) = n0 + S m`{.fact} 로 일반화한다:
- 경우 1 (기저): `0 + S m = 0 + S m`{.claim} 임을 보이자.
  - eq (eq_refl) 의 정의에 의해, `0 + S m = 0 + S m`{.claim} 이다 *by Corelib.Init.Logic.eq_refl*.
- 경우 2 (귀납): `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim} 임을 보이자.
  - 임의의 `n0 : nat`{.var}.
    - 귀납 가정에 의해 `S (n0 + m) = n0 + S m`{.hyp} (IH) 라고 가정하자.
      - eq (eq_refl) 의 정의에 의해, `S (n0 + S m) = S (n0 + S m)`{.claim} 이다 *by Corelib.Init.Logic.eq_refl*.
      - IH 에 의해 `S (n0 + m) = n0 + S m`{.claim} 이다.
      - `S (n0 + m) = n0 + S m`{.fact} 오른쪽에서 왼쪽으로 (eq_ind_r) 을(를) 이용하여 다시 쓰면, `S (S (n0 + m)) = S (n0 + S m)`{.claim} 임을 얻는다.
- 이 경우들이 전부이므로, 따라서 `forall n0 : nat, S (n0 + m) = n0 + S m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- 특히 `S (n + m) = n + S m`{.claim}.
