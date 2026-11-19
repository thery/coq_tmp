---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Let `m : nat`{.var}. We prove `m + 0 = m`{.claim}.

- We prove `m + 0 = m`{.fact} by induction on `m`{.fact} (nat, nat_ind):
- Case 1 (base): we prove `0 + 0 = 0 + 0`{.claim}.
  - By definition of eq (eq_refl), we have `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Let us consider an arbitrary `m0 : nat`{.var}.
    - Assume by induction hypothesis `m0 + 0 = m0`{.hyp} (IH).
      - By IH we have `m0 + 0 = m0`{.claim}.
      - Using f_equal we get `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
      - We deduce `S (m0 + 0) = S m0`{.claim}.
- These cases being exhaustive, we deduce `m + 0 = m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
