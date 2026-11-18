---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ko
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

`A B C : Prop`{.var} 라 하자. `A -> B -> C`{.hyp} (h) 그리고 `A -> B`{.hyp} (h0) 그리고 `A`{.hyp} (h1) 라고 가정하자. `C`{.claim} 임을 보이자.

- h1 에 의해 `A`{.claim} 이다.
- h1 에 의해 `A`{.claim} 이다.
- h0 에 의해 `A -> B`{.claim} 이다.
- h 에 의해 `A -> B -> C`{.claim} 이다.
- 따라서 `C`{.claim} *by tauto*.
