---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# le_0_m

We prove `forall m : nat, 0 <= m`{.claim}.

- We prove `forall n : nat, 0 <= n` by induction (nat, *nat_ind*{.just}):
  - Case 1 (base): we prove `0 <= 0`{.claim}.
    - By definition of le (*le_n*{.just}), we have `0 <= 0`{.claim}.
  - Case 2 (inductive): we prove `forall m : nat, 0 <= m -> 0 <= S m`{.claim}.
    - Let us consider an arbitrary `m : nat`{.var}. Assume by induction hypothesis `0 <= m`{.hyp} (h). By definition of le (*le_S*{.just}) with witness `m`, from *h*{.just} we deduce `0 <= S m`{.claim}.

  These cases being exhaustive, we deduce `forall n : nat, 0 <= n`{.claim}.
