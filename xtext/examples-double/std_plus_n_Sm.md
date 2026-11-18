---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm

Let `n m : nat`{.var}. We prove `S (n + m) = n + S m`{.claim}.

- To prove `S (n + m) = n + S m`{.fact} by induction (nat, nat_ind), we generalise it to `forall n0 : nat, S (n0 + m) = n0 + S m`{.fact}:
- Case 1 (base): we prove `S (0 + m) = 0 + S m`{.claim}.
  - By definition of eq (eq_refl), we have `S m = S m`{.claim} *by eapply @eq_refl; eauto*.
- Case 2 (inductive): we prove `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
  - Let us consider an arbitrary `n0 : nat`{.var}.
    - Assume by induction hypothesis `S (n0 + m) = n0 + S m`{.hyp} (IHn).
      - By IHn we have `S (n0 + m) = n0 + S m`{.claim}.
      - Using f_equal_nat we get `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y`{.claim} *by exact @Corelib.Init.Peano.f_equal_nat*.
      - We deduce `S (S (n0 + m)) = S (n0 + S m)`{.claim}.
- These cases being exhaustive, we deduce `forall n0 : nat, S (n0 + m) = n0 + S m`{.claim} *by eapply (@nat_ind (fun n0 : nat => S (n0 + m) = n0 + S m)); cbv beta; eauto*.
- In particular `S (n + m) = n + S m`{.claim}.
