---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ko
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

`n m : nat`{.var} 라 하자. `S (n + m) = n + S m`{.claim} 임을 보이자.

- `S (n + m) = n + S m` 임을 보이자 *n*{.just} (*nat*{.just}, *induction*{.just}) 에 대한 귀납법으로:
  - 경우 1 (기저): `0 + S m = 0 + S m`{.claim} 임을 보이자.
    - eq (*eq_refl*{.just}) 의 정의에 의해, `0 + S m = 0 + S m`{.claim} 이다.
  - 경우 2 (귀납): `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim} 임을 보이자.
    - 임의로 택한 `n0 : nat`{.var}; 귀납 가정에 의해 `S (n0 + m) = n0 + S m`{.hyp} (IH) 라고 가정하자.
      - eq (*eq_refl*{.just}) 의 정의에 의해, `S (n0 + S m) = S (n0 + S m)`{.claim} 이다.
      - *IH*{.just} 에 의해 `S (n0 + m) = n0 + S m`{.claim} 이다.

      `S (n0 + m) = n0 + S m`{.fact} 오른쪽에서 왼쪽으로 (eq_ind_r) 을(를) 이용하여 다시 쓰면, `S (S (n0 + m)) = S (n0 + S m)`{.claim} 임을 얻는다.

  이 경우들이 전부이므로, 따라서 `S (n + m) = n + S m`{.claim}.
