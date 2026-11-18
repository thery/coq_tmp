---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ko
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

`A B : Prop`{.var} 라 하자. `A \/ B`{.hyp} (h) 라고 가정하자. `B \/ A`{.claim} 임을 보이자.

- `B \/ A`{.fact} 임을 보이자 `A \/ B`{.fact} (h) (or, or_ind) 에 대한 경우 분석으로:
- 경우 1: `A -> B \/ A`{.claim} 임을 보이자.
  - `A`{.hyp} (i) 라고 가정하자.
    - or (or_intror) 의 정의에 의해, `A`{.fact} (i) 로부터 따라서 `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- 경우 2: `B -> B \/ A`{.claim} 임을 보이자.
  - `B`{.hyp} (j) 라고 가정하자.
    - or (or_introl) 의 정의에 의해, `B`{.fact} (j) 로부터 따라서 `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- `B \/ A`{.claim} 모든 경우에 이다.
