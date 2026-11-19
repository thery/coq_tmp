---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Siano `A B C : Prop`{.var}. Supponiamo `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) e `A`{.hyp} (h1). Dimostriamo `C`{.claim}.

- Per *h1*{.just} abbiamo `A`{.claim}.
- Applicando *h0*{.just} a *h1*{.just}, abbiamo `B`{.claim}.
- Applicando *h*{.just}, abbiamo `C`{.claim}.
