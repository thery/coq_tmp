---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Sint `A B C D : Prop`{.var}. Ponamus `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) et `A`{.hyp} (h4). Ostendamus `D`{.claim}.

- Per h4 habemus `A`{.claim}.
- Applicando h2, habemus `B`{.claim}.
  - Per h4 habemus `A`{.claim}.
  - Applicando h3 ad h4, habemus `C`{.claim}.
- Applicando h3 ad h4, habemus `C`{.claim}.
- Applicando h1, habemus `D`{.claim}.
