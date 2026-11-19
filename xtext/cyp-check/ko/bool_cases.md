---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ko
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

`b : bool`{.var} 라 하자. `b = true \/ b = false`{.claim} 임을 보이자.

- `b = true \/ b = false` 임을 보이자 `b` (bool, match) 에 대한 경우 분석으로:
  - 경우 1: `true = true \/ true = false`{.claim} 임을 보이자.
    - eq (*eq_refl*{.just}) 의 정의에 의해, `true = true`{.claim} 이다.
    - or (*or_introl*{.just}) 의 정의에 의해, `true = true \/ true = false`{.claim} 이다.
  - 경우 2: `false = true \/ false = false`{.claim} 임을 보이자.
    - eq (*eq_refl*{.just}) 의 정의에 의해, `false = false`{.claim} 이다.
    - or (*or_intror*{.just}) 의 정의에 의해, `false = true \/ false = false`{.claim} 이다.

  이 경우들이 전부이므로, 따라서 `b = true \/ b = false`{.claim}.
