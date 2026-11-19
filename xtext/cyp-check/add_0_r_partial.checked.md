---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r_partial (proof in progress)

✅ Let `n : nat`{.var}. We prove `n + 0 = n`{.claim}.

- ✅ We prove `n + 0 = n` by induction on *n*{.just} (*nat*{.just}, *induction*{.just}):
  - ✅ Case 1 (base): we prove `0 = 0`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `0 = 0`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
    - 🔶 **[1.2.1]** Let us choose arbitrarily `m : nat`{.var}; assume by induction hypothesis `m + 0 = m`{.hyp} (IH). Prove `S m + 0 = S m`{.goal}.

      <details><summary>open goal of the text, not tried: condition 1.2.1, to prove in the Proof block: S m + 0 = S m</summary></details>


  These cases being exhaustive, we deduce `n + 0 = n`{.claim}.
