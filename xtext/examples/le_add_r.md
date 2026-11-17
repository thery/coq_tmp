---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# le_add_r'

Let `n m : nat`{.var}. We prove `n <= n + m`{.claim}.

- To prove `n <= n + m`{.fact} by induction (nat, nat_ind), we generalise it to `forall n0 : nat, n <= n + n0`{.fact}:
- Case 1 (base): we prove `n <= n + 0`{.claim}.
  - By definition of le (le_n), we have `n <= n`{.claim} *by eapply @le_n; eauto*.
  - In particular `n + 0 = n`{.claim}.
    - Using add_0_r we get `forall n0 : nat, n0 + 0 = n0`{.claim} *by exact @add_0_r*.
  - Rewriting with `n + 0 = n`{.fact} from right to left (eq_ind_r), we get `n <= n + 0`{.claim}.
- Case 2 (inductive): we prove `forall m0 : nat, n <= n + m0 -> n <= n + S m0`{.claim}.
  - Let us consider an arbitrary `m0 : nat`{.var}.
    - Assume by induction hypothesis `n <= n + m0`{.hyp} (IH).
      - By definition of le (le_S) with witness `n + m0`{.fact}, from `n <= n + m0`{.fact} (IH) we deduce `n <= S (n + m0)`{.claim} *by eapply @le_S; eauto*.
      - In particular `n + S m0 = S (n + m0)`{.claim}.
        - Using add_succ_r we get `forall n0 m1 : nat, n0 + S m1 = S (n0 + m1)`{.claim} *by exact @add_succ_r*.
      - Rewriting with `n + S m0 = S (n + m0)`{.fact} from right to left (eq_ind_r), we get `n <= n + S m0`{.claim}.
- These cases being exhaustive, we deduce `forall n0 : nat, n <= n + n0`{.claim} *by eapply (@nat_ind (fun m0 : nat => n <= n + m0)); cbv beta; eauto*.
- In particular `n <= n + m`{.claim}.
