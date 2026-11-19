---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ko
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

`A B C D : Prop`{.var} 라 하자. `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) 그리고 `A`{.hyp} (h4) 라고 가정하자. `D`{.claim} 임을 보이자.

- *h4*{.just} 에 의해 `A`{.claim} 이다.
- 적용하여 *h2*{.just}, `B`{.claim} 이다.
  - *h4*{.just} 에 의해 `A`{.claim} 이다.
  - 적용하여 *h3*{.just} 에 *h4*{.just}, `C`{.claim} 이다.
- 적용하여 *h3*{.just} 에 *h4*{.just}, `C`{.claim} 이다.
- 적용하여 *h1*{.just}, `D`{.claim} 이다.
