---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ko
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

`x y z t : Prop`{.var} 라 하자. `(x -> z) /\ (y -> t)`{.hyp} (h1) 그리고 `x /\ y`{.hyp} (h2) 라고 가정하자. `z /\ t`{.claim} 임을 보이자.

- and (*and_ind*{.just}) *h1*{.just} 에서 의 정의로 돌아가서, `z /\ t`{.claim} 임을 보이자:
  - `x -> z`{.hyp} (i) 그리고 `y -> t`{.hyp} (j) 라고 가정하자. and (*and_ind*{.just}) *h2*{.just} 에서 의 정의로 돌아가서, `z /\ t`{.claim} 임을 보이자:
    - `x`{.hyp} (k) 그리고 `y`{.hyp} (l) 라고 가정하자.
      - 적용하여 *i*{.just} 에 *k*{.just}, `z`{.claim} 이다.
      - 적용하여 *j*{.just} 에 *l*{.just}, `t`{.claim} 이다.

      그러므로 and (*conj*{.just}) 의 정의에 의해, `z /\ t`{.claim} 이다.
