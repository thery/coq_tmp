---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# forall_and

✅ Let `P Q : nat -> Prop`{.var}. Assume `forall x : nat, P x /\ Q x`{.hyp} (H). Let `x : nat`{.var}. We prove `P x`{.claim}.

- ✅ In particular `P x /\ Q x`{.claim} (a).
  - ✅ By H we have `forall x0 : nat, P x0 /\ Q x0`{.claim}.
- ✅ Going back to the definition of and (match) in `P x /\ Q x`{.fact} (a), we prove `P x`{.claim}:
  - ▫️ Assume `P x`{.hyp} (p) and `Q x`{.hyp} (_H).
    - ✅ By p we have `P x`{.claim}.
