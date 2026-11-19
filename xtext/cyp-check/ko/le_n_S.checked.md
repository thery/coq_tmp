---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ko
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ `n m : nat`{.var} 라 하자. `n <= m`{.hyp} (H) 라고 가정하자. `S n <= S m`{.claim} 임을 보이자.

- ✅ `S n <= S m` 임을 보이자 *H*{.just} (*le*{.just}, *induction*{.just}) 에 대한 귀납법으로:
  - ✅ 경우 1 (기저): `S n <= S n`{.claim} 임을 보이자.
    - ✅ le (*le_n*{.just}) 의 정의에 의해, `S n <= S n`{.claim} 이다.
  - ✅ 경우 2 (귀납): `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim} 임을 보이자.
    - ✅ 임의로 택한 `m0 : nat`{.var}; `n <= m0`{.hyp} (H0) 그리고 귀납 가정에 의해 `S n <= S m0`{.hyp} (IH) 라고 가정하자. le (*le_S*{.just}) 의 정의에 의해 증인 `S m0`, *IH*{.just} 로부터 따라서 `S n <= S (S m0)`{.claim}.

  `S n <= S m`{.claim} 모든 경우에 이다.
