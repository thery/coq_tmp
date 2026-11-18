---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Let `A B C : Prop`{.var}. Assume `A -> B -> C`{.hyp} (h) and `A -> B`{.hyp} (h0) and `A`{.hyp} (h1). We prove `C`{.claim}.

- ✅ By h1 we have `A`{.claim}.
- ✅ By h1 we have `A`{.claim}.
- ✅ By h0 we have `A -> B`{.claim}.
- ✅ By h we have `A -> B -> C`{.claim}.
- ✅ We deduce `C`{.claim} *by tauto*.
