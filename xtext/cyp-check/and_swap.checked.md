---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# and_swap

✅ Let `A B : Prop`{.var}. Assume `A /\ B`{.hyp} (H). We prove `B /\ A`{.claim}.

- ✅ Going back to the definition of *and*{.just} (*match*{.just}) in *H*{.just}, we prove `B /\ A`{.claim}:
  - ✅ Assume `A`{.hyp} (a) and `B`{.hyp} (b). By definition of and (*conj*{.just}), from *b*{.just} and *a*{.just} we deduce `B /\ A`{.claim}.
