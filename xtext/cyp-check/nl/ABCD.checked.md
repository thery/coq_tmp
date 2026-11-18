---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: nl
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Laat `A B C D : Prop`{.var}. Stel `A -> B -> C -> D`{.hyp} (h1) en `A -> C -> B`{.hyp} (h2) en `A -> C`{.hyp} (h3) en `A`{.hyp} (h4). We bewijzen `D`{.claim}.

- ✅ Volgens h4 er geldt `A`{.claim}.
- ✅ Volgens h4 er geldt `A`{.claim}.
- ✅ Volgens h4 er geldt `A`{.claim}.
- ✅ Volgens h3 er geldt `A -> C`{.claim}.
- ✅ Volgens h2 er geldt `A -> C -> B`{.claim}.
- ✅ Volgens h4 er geldt `A`{.claim}.
- ✅ Volgens h3 er geldt `A -> C`{.claim}.
- ✅ Volgens h1 er geldt `A -> B -> C -> D`{.claim}.
- ✅ Hieruit volgt `D`{.claim} *by tauto*.
