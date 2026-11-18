---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Let `A B C : Prop`{.var}. Assume `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) and `A`{.hyp} (h1). We prove `C`{.claim}.

- ✅ By h1 we have `A`{.claim}.
- ✅ Applying h0 to h1, we have `B`{.claim}.
- ✅ Applying h, we have `C`{.claim}.
