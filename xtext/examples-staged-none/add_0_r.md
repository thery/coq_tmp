---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Let `n : nat`{.var}. We prove `n + 0 = n`{.claim}.

- We prove `n + 0 = n` by induction on `n` (nat, *nat_ind*{.just}):
  - Case 1 (base): we prove `0 = 0`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `0 = 0`{.claim}.
  - Case 2 (inductive): we prove `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
    - Let us choose arbitrarily `m : nat`{.var}. Assume `m + 0 = m`{.hyp} (IH).
      - By definition of eq (*eq_refl*{.just}), we have `S m = S m`{.claim}.
      - By *IH*{.just} we have `m + 0 = m`{.claim}.

      Rewriting with `m + 0 = m`{.fact} from right to left (eq_ind_r), we get `S (m + 0) = S m`{.claim}.

  These cases being exhaustive, we deduce `n + 0 = n`{.claim}.
