---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# le_0_n'

✅ We prove `forall n : nat, 0 <= n`{.claim}.

- ✅ We prove `forall n : nat, 0 <= n`{.claim} by recursion on `n` (fix le_0_n'):
  - ✅ Let us choose arbitrarily `n : nat`{.var}. We prove `0 <= n` by induction on `n` (nat, match):
    - ✅ Case 1 (base): we prove `0 <= 0`{.claim}.
      - ✅ By definition of le (*le_n*{.just}), we have `0 <= 0`{.claim}.
    - ✅ Case 2 (inductive): we prove `forall m : nat, 0 <= S m`{.claim}.
      - ✅ Let us choose arbitrarily `m : nat`{.var}.
        - ✅ By induction hypothesis (the recursive call le_0_n') we have `forall n0 : nat, 0 <= n0`{.claim}.
        - ✅ In particular `0 <= m`{.claim}.

        By definition of le (*le_S*{.just}) with witness `m`, we have `0 <= S m`{.claim}.

    These cases being exhaustive, we deduce `0 <= n`{.claim}.
