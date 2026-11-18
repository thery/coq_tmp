---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Tauto

Let `A B C : Prop`{.var}. Assume `A`{.hyp} (h1) and `B`{.hyp} (h2) and `A -> B -> C`{.hyp} (h3). We prove `C`{.claim}.

- By h1 we have `A`{.claim}.
- By h2 we have `B`{.claim}.
- By h3 we have `A -> B -> C`{.claim}.
- We deduce `C`{.claim}.
