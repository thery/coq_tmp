---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Soient `A B C : Prop`{.var}. Supposons `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) et `A`{.hyp} (h1). Montrons `C`{.claim}.

- Par h1 nous avons `A`{.claim}.
- En appliquant h0 à h1, nous avons `B`{.claim}.
- En appliquant h, nous avons `C`{.claim}.
