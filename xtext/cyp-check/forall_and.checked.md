---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# forall_and

✅ Let `P Q : nat -> Prop`{.var}. Assume `forall x : nat, P x /\ Q x`{.hyp} (H). Let `x : nat`{.var}. We prove `P x`{.claim}.

- ✅ Applying *H*{.just} to x, we have `P x /\ Q x`{.claim} (a).
- ✅ Going back to the definition of *and*{.just} (*match*{.just}) in *a*{.just}, we prove `P x`{.claim}:
  - ✅ Assume `P x`{.hyp} (p) and `Q x`{.hyp} (_H). By *p*{.just} we have `P x`{.claim}.
