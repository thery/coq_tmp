---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ko
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

`A : Set`{.var} 라 하자. `P : A -> Prop`{.var} 라 하자. `y : A`{.var} 라 하자. `exists x : A, P x -> forall z : A, P z`{.claim} 임을 보이자.

- 특히 `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - classic 을(를) 이용하여 `forall P0 : Prop, P0 \/ ~ P0`{.claim} 임을 얻는다 *by Stdlib.Logic.Classical_Prop.classic*.
- `exists x : A, P x -> forall z : A, P z`{.fact} 임을 보이자 `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match) 에 대한 경우 분석으로:
- 경우 1: `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim} 임을 보이자.
  - `forall z : A, P z`{.hyp} (H) 라고 가정하자.
    - `P y`{.hyp} (_H) 라고 가정하자.
      - H 에 의해 `forall z : A, P z`{.claim} 이다.
    - `P y -> forall z : A, P z`{.claim} 임을 보였다.
    - ex (ex_intro) 의 정의에 의해 증인 `y`{.fact}, `exists x : A, P x -> forall z : A, P z`{.claim} 이다 *by Corelib.Init.Logic.ex_intro*.
- 경우 2: `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim} 임을 보이자.
  - `~ (forall z : A, P z)`{.hyp} (H) 라고 가정하자.
    - 따라서 `exists n : A, ~ P n`{.claim} (e).
      - H 에 의해 `~ (forall z : A, P z)`{.claim} 이다.
      - not_all_ex_not 을(를) 이용하여 `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} 임을 얻는다 *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - ex (match) `exists n : A, ~ P n`{.fact} (e) 에서 의 정의로 돌아가서, `exists x : A, P x -> forall z : A, P z`{.claim} 임을 보이자:
      - 임의의 `t : A`{.var}.
        - `~ P t`{.hyp} (i) 라고 가정하자.
          - `P t`{.hyp} (h) 라고 가정하자.
            - 따라서 `False`{.claim} (f).
              - h 에 의해 `P t`{.claim} 이다.
              - i 에 의해 `~ P t`{.claim} 이다, 즉 `P t -> False`{.fact}.
            - 모순에 의해 (False, match), `False`{.fact} (f) 로부터 `forall z : A, P z`{.claim} 임을 유도할 수 있다.
          - `P t -> forall z : A, P z`{.claim} 임을 보였다.
          - ex (ex_intro) 의 정의에 의해 증인 `t`{.fact}, `exists x : A, P x -> forall z : A, P z`{.claim} 이다 *by Corelib.Init.Logic.ex_intro*.
- `exists x : A, P x -> forall z : A, P z`{.claim} 모든 경우에 이다.
