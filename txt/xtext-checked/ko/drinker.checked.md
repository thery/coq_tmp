---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ko
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ `A : Set`{.var} 라 하자. `P : A -> Prop`{.var} 라 하자. `y : A`{.var} 라 하자. `exists x : A, P x -> forall z : A, P z`{.claim} 임을 보이자.

- ✅ 적용하여 *Classical_Prop.classic*{.just}, `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o) 이다.
  - ▫️ 원소 `forall z : A, P z` 에 속한다 `Prop`.
- ✅ `exists x : A, P x -> forall z : A, P z` 임을 보이자 *o*{.just} (or, match) 에 대한 경우 분석으로:
  - ✅ 경우 1: `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim} 임을 보이자.
    - ✅ `forall z : A, P z`{.hyp} (H) 라고 가정하자.
      - ✅ `P y`{.hyp} (_H) 라고 가정하자. *H*{.just} 에 의해 `forall z : A, P z`{.claim} 이다.
      - ✅ `P y -> forall z : A, P z`{.claim} 임을 보였다.

      ex (*ex_intro*{.just}) 의 정의에 의해 증인 `y`, `exists x : A, P x -> forall z : A, P z`{.claim} 이다.
  - ✅ 경우 2: `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim} 임을 보이자.
    - ✅ `~ (forall z : A, P z)`{.hyp} (H) 라고 가정하자.
      - ✅ 적용하여 *Classical_Pred_Type.not_all_ex_not*{.just} 에 A, P 그리고 *H*{.just}, `exists n : A, ~ P n`{.claim} (e) 이다.
      - ✅ ex (match) *e*{.just} 에서 의 정의로 돌아가서, `exists x : A, P x -> forall z : A, P z`{.claim} 임을 보이자:
        - ✅ 임의로 택한 `t : A`{.var}; `~ P t`{.hyp} (i) 라고 가정하자.
          - ✅ `P t`{.hyp} (h) 라고 가정하자.
            - ✅ 적용에 의해, 와 함께 *h*{.just}, `False`{.claim} (f) 이다.
              - ✅ *i*{.just} 에 의해 `~ P t` 이다, 즉 `P t -> False`{.claim}.

            모순에 의해 (False, match), *f*{.just} 로부터 `forall z : A, P z`{.claim} 임을 유도할 수 있다.
          - ✅ `P t -> forall z : A, P z`{.claim} 임을 보였다.

          ex (*ex_intro*{.just}) 의 정의에 의해 증인 `t`, `exists x : A, P x -> forall z : A, P z`{.claim} 이다.

      `exists x : A, P x -> forall z : A, P z`{.claim} 이다.

  `exists x : A, P x -> forall z : A, P z`{.claim} 모든 경우에 이다.
