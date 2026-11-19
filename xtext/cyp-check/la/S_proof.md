---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Sint `A B C : Prop`{.var}. Ponamus `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) et `A`{.hyp} (h1). Ostendamus `C`{.claim}.

- Per *h1*{.just} habemus `A`{.claim}.
- Applicando *h0*{.just} ad *h1*{.just}, habemus `B`{.claim}.
- Applicando *h*{.just}, habemus `C`{.claim}.
