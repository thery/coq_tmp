---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Soient `A B C : Prop`{.var}. Supposons `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) et `A`{.hyp} (h1). Montrons `C`{.claim}.

- Par *h1*{.just} nous avons `A`{.claim}.
- En appliquant *h0*{.just} à *h1*{.just}, nous avons `B`{.claim}.
- En appliquant *h*{.just}, nous avons `C`{.claim}.
