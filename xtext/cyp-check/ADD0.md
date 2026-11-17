---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Let `m : nat`{.var}. We prove `m + 0 = m`{.claim}.

- To prove `m + 0 = m`{.fact} by induction (nat, nat_ind), we generalise it to `forall n : nat, n + 0 = n`{.fact}:
- Case 1 (base): we prove `0 + 0 = 0 + 0`{.claim}.
  - By definition of eq (eq_refl), we have `0 + 0 = 0 + 0`{.claim} *by eapply @eq_refl; eauto*.
- Case 2 (inductive): we prove `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Let us consider an arbitrary `m0 : nat`{.var}.
    - Assume by induction hypothesis `m0 + 0 = m0`{.hyp} (IH).
      - By IH we have `m0 + 0 = m0`{.claim}.
      - Using f_equal we get `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by exact @Corelib.Init.Logic.f_equal*.
      - We deduce `S (m0 + 0) = S m0`{.claim}.
- These cases being exhaustive, we deduce `forall n : nat, n + 0 = n`{.claim} *by eapply (@nat_ind (fun m0 : nat => m0 + 0 = m0)); cbv beta; eauto*.
- In particular `m + 0 = m`{.claim}.
