---
require: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Let `n : nat`{.var}. We prove `n + 0 = n`{.claim}.

- To prove `n + 0 = n`{.fact} by induction (nat, nat_ind), we generalise it to `forall n0 : nat, n0 + 0 = n0`{.fact}:
- Case 1 (base): we prove `0 = 0`{.claim}.
  - By definition of eq (eq_refl), we have `0 = 0`{.claim} *by eapply @eq_refl; eauto*.
- Case 2 (inductive): we prove `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - Let us consider an arbitrary `m : nat`{.var}.
    - Assume by induction hypothesis `m + 0 = m`{.hyp} (IH).
      - By definition of eq (eq_refl), we have `S m = S m`{.claim} *by eapply @eq_refl; eauto*.
      - By IH we have `m + 0 = m`{.claim}.
      - Rewriting with `m + 0 = m`{.fact} from right to left (eq_ind_r), we get `S (m + 0) = S m`{.claim}.
- These cases being exhaustive, we deduce `forall n0 : nat, n0 + 0 = n0`{.claim}.
- In particular `n + 0 = n`{.claim}.
