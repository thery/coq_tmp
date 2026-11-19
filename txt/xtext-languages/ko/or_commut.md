---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ko
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

`A B : Prop`{.var} 라 하자. `A \/ B`{.hyp} (h) 라고 가정하자. `B \/ A`{.claim} 임을 보이자.

- `B \/ A` 임을 보이자 *h*{.just} (or, *or_ind*{.just}) 에 대한 경우 분석으로:
  - 경우 1: `A -> B \/ A`{.claim} 임을 보이자.
    - `A`{.hyp} (i) 라고 가정하자. or (*or_intror*{.just}) 의 정의에 의해, *i*{.just} 로부터 따라서 `B \/ A`{.claim}.
  - 경우 2: `B -> B \/ A`{.claim} 임을 보이자.
    - `B`{.hyp} (j) 라고 가정하자. or (*or_introl*{.just}) 의 정의에 의해, *j*{.just} 로부터 따라서 `B \/ A`{.claim}.

  `B \/ A`{.claim} 모든 경우에 이다.
