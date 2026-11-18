---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: fr
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Soient `A B C D : Prop`{.var}. Supposons `A -> B -> C -> D`{.hyp} (h1) et `A -> C -> B`{.hyp} (h2) et `A -> C`{.hyp} (h3) et `A`{.hyp} (h4). Montrons `D`{.claim}.

- ✅ Par h4 nous avons `A`{.claim}.
- ✅ Par h4 nous avons `A`{.claim}.
- ✅ Par h4 nous avons `A`{.claim}.
- ✅ Par h3 nous avons `A -> C`{.claim}.
- ✅ Par h2 nous avons `A -> C -> B`{.claim}.
- ✅ Par h4 nous avons `A`{.claim}.
- ✅ Par h3 nous avons `A -> C`{.claim}.
- ✅ Par h1 nous avons `A -> B -> C -> D`{.claim}.
- ✅ Nous en déduisons `D`{.claim} *by tauto*.
