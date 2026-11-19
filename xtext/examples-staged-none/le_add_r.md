---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# le_add_r'

Let `n m : nat`{.var}. We prove `n <= n + m`{.claim}.

- We prove `n <= n + m` by induction on *m*{.just} (*nat*{.just}, *induction*{.just}):
  - Case 1 (base): we prove `n <= n + 0`{.claim}.
    - By definition of le (*le_n*{.just}), we have `n <= n`{.claim}.
    - By application, we have `n + 0 = n`{.claim}.
      - By *PeanoNat.Nat.add_0_r*{.just} we have `forall n0 : nat, n0 + 0 = n0`{.claim}.
    - Rewriting with `n + 0 = n`{.fact} from right to left (eq_ind_r), we get `n <= n + 0`{.claim}.
  - Case 2 (inductive): we prove `forall m0 : nat, n <= n + m0 -> n <= n + S m0`{.claim}.
    - Let us choose arbitrarily `m0 : nat`{.var}. Assume `n <= n + m0`{.hyp} (IH).
      - By definition of le (*le_S*{.just}) with witness `n + m0`, from *IH*{.just} we deduce `n <= S (n + m0)`{.claim}.
      - By application, we have `n + S m0 = S (n + m0)`{.claim}.
        - By application, we have `forall m1 : nat, n + S m1 = S (n + m1)`{.claim}.
          - By *PeanoNat.Nat.add_succ_r*{.just} we have `forall n0 m1 : nat, n0 + S m1 = S (n0 + m1)`{.claim}.

      Rewriting with `n + S m0 = S (n + m0)`{.fact} from right to left (eq_ind_r), we get `n <= n + S m0`{.claim}.

  These cases being exhaustive, we deduce `n <= n + m`{.claim}.
