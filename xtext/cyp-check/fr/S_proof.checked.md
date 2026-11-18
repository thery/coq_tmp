---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Soient `A B C : Prop`{.var}. Supposons `A -> B -> C`{.hyp} (h) et `A -> B`{.hyp} (h0) et `A`{.hyp} (h1). Montrons `C`{.claim}.

- ✅ Par h1 nous avons `A`{.claim}.
- ✅ Par h1 nous avons `A`{.claim}.
- ✅ Par h0 nous avons `A -> B`{.claim}.
- ✅ Par h nous avons `A -> B -> C`{.claim}.
- ✅ Nous en déduisons `C`{.claim} *by tauto*.
