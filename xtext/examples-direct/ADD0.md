---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Let `m : nat`{.var}. We prove `m + 0 = m`{.claim}.

- We prove `m + 0 = m` by induction on `m` (nat, *nat_ind*{.just}):
  - Case 1 (base): we prove `0 + 0 = 0 + 0`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `0 + 0 = 0 + 0`{.claim}.
  - Case 2 (inductive): we prove `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - Let us consider an arbitrary `m0 : nat`{.var}. Assume by induction hypothesis `m0 + 0 = m0`{.hyp} (IH).
      - By *IH*{.just} we have `m0 + 0 = m0`{.claim}.
      - Using *f_equal*{.just} we get `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim}.

      We deduce `S (m0 + 0) = S m0`{.claim}.

  These cases being exhaustive, we deduce `m + 0 = m`{.claim}.
