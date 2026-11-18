---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Tauto

✅ Let `A B C : Prop`{.var}. Assume `A`{.hyp} (h1), `B`{.hyp} (h2) and `A -> B -> C`{.hyp} (h3). We prove `C`{.claim}.

- ✅ Applying h3 to h1 and h2, we have `C`{.claim}.
