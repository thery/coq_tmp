---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Laat `A B C : Prop`{.var}. Stel `A -> B -> C`{.hyp} (h) en `A -> B`{.hyp} (h0) en `A`{.hyp} (h1). We bewijzen `C`{.claim}.

- ✅ Volgens h1 er geldt `A`{.claim}.
- ✅ Volgens h1 er geldt `A`{.claim}.
- ✅ Volgens h0 er geldt `A -> B`{.claim}.
- ✅ Volgens h er geldt `A -> B -> C`{.claim}.
- ✅ Hieruit volgt `C`{.claim} *by tauto*.
