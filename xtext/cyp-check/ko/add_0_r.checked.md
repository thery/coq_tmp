---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: ko
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

✅ `n : nat`{.var} 라 하자. `n + 0 = n`{.claim} 임을 보이자.

- ✅ `n + 0 = n` 임을 보이자 `n` (nat, *nat_ind*{.just}) 에 대한 귀납법으로:
  - ✅ 경우 1 (기저): `0 = 0`{.claim} 임을 보이자.
    - ✅ eq (*eq_refl*{.just}) 의 정의에 의해, `0 = 0`{.claim} 이다.
  - ✅ 경우 2 (귀납): `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim} 임을 보이자.
    - ✅ 임의로 택한 `m : nat`{.var}; 귀납 가정에 의해 `m + 0 = m`{.hyp} (IH) 라고 가정하자.
      - ✅ eq (*eq_refl*{.just}) 의 정의에 의해, `S m = S m`{.claim} 이다.
      - ✅ *IH*{.just} 에 의해 `m + 0 = m`{.claim} 이다.

      `m + 0 = m`{.fact} 오른쪽에서 왼쪽으로 (eq_ind_r) 을(를) 이용하여 다시 쓰면, `S (m + 0) = S m`{.claim} 임을 얻는다.

  이 경우들이 전부이므로, 따라서 `n + 0 = n`{.claim}.
