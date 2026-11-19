---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: fr
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Soient `A B C D : Prop`{.var}. Supposons `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) et `A`{.hyp} (h4). Montrons `D`{.claim}.

- ✅ Par *h4*{.just} nous avons `A`{.claim}.
- ✅ En appliquant *h2*{.just}, nous avons `B`{.claim}.
  - ✅ Par *h4*{.just} nous avons `A`{.claim}.
  - ✅ En appliquant *h3*{.just} à *h4*{.just}, nous avons `C`{.claim}.
- ✅ En appliquant *h3*{.just} à *h4*{.just}, nous avons `C`{.claim}.
- ✅ En appliquant *h1*{.just}, nous avons `D`{.claim}.
