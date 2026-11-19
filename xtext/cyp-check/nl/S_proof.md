---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Laat `A B C : Prop`{.var}. Stel `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) en `A`{.hyp} (h1). We bewijzen `C`{.claim}.

- Volgens *h1*{.just} er geldt `A`{.claim}.
- Door toepassing van *h0*{.just} op *h1*{.just}, er geldt `B`{.claim}.
- Door toepassing van *h*{.just}, er geldt `C`{.claim}.
