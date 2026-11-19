---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ko
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ `A B C : Prop`{.var} 라 하자. `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) 그리고 `A`{.hyp} (h1) 라고 가정하자. `C`{.claim} 임을 보이자.

- ✅ *h1*{.just} 에 의해 `A`{.claim} 이다.
- ✅ 적용하여 *h0*{.just} 에 *h1*{.just}, `B`{.claim} 이다.
- ✅ 적용하여 *h*{.just}, `C`{.claim} 이다.
