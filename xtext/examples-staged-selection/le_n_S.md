---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

Let `n m : nat`{.var}. Assume `n <= m`{.hyp} (H). We prove `S n <= S m`{.claim}.

- We prove `S n <= S m` by induction on *H*{.just} (le, le_ind):
  - Case 1 (base): we prove `S n <= S n`{.claim}.
    - By definition of le (*le_n*{.just}), we have `S n <= S n`{.claim}.
  - Case 2 (inductive): we prove `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
    - Let us choose arbitrarily `m0 : nat`{.var}; assume `n <= m0`{.hyp} (H0) and by induction hypothesis `S n <= S m0`{.hyp} (IH). By definition of le (*le_S*{.just}) with witness `S m0`, from *IH*{.just} we deduce `S n <= S (S m0)`{.claim}.

  We have `S n <= S m`{.claim} in all cases.
