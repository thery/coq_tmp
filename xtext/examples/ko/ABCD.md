---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ko
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

`A B C D : Prop`{.var} 라 하자. `A -> B -> C -> D`{.hyp} (h1) 그리고 `A -> C -> B`{.hyp} (h2) 그리고 `A -> C`{.hyp} (h3) 그리고 `A`{.hyp} (h4) 라고 가정하자. `D`{.claim} 임을 보이자.

- h4 에 의해 `A`{.claim} 이다.
- h4 에 의해 `A`{.claim} 이다.
- h4 에 의해 `A`{.claim} 이다.
- h3 에 의해 `A -> C`{.claim} 이다.
- h2 에 의해 `A -> C -> B`{.claim} 이다.
- h4 에 의해 `A`{.claim} 이다.
- h3 에 의해 `A -> C`{.claim} 이다.
- h1 에 의해 `A -> B -> C -> D`{.claim} 이다.
- 따라서 `D`{.claim} *by tauto*.
