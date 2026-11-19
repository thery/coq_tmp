---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Laat `A B C : Prop`{.var}. Stel `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) en `A`{.hyp} (h1). We bewijzen `C`{.claim}.

- ✅ Volgens h1 er geldt `A`{.claim}.
- ✅ Door toepassing van h0 op h1, er geldt `B`{.claim}.
- ✅ Door toepassing van h, er geldt `C`{.claim}.
