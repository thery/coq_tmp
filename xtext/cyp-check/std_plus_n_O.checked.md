---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_O

✅ Let `n : nat`{.var}. We prove `n = n + 0`{.claim}.

- ▫️ To prove `n = n + 0`{.fact} by induction (nat, nat_ind), we generalise it to `forall n0 : nat, n0 = n0 + 0`{.fact}:
- ✅ Case 1 (base): we prove `0 = 0 + 0`{.claim}.
  - ✅ By definition of eq (eq_refl), we have `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Case 2 (inductive): we prove `forall n0 : nat, n0 = n0 + 0 -> S n0 = S n0 + 0`{.claim}.
  - ▫️ Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `n0 = n0 + 0`{.hyp} (IHn).
    - ▫️ The element `nat`{.fact} belongs to `Type`{.fact}.
    - ▫️ The element `S`{.fact} belongs to `nat -> nat`{.fact}.
    - ▫️ The element `n0`{.fact} belongs to `nat`{.fact}.
    - ▫️ The element `n0 + 0`{.fact} belongs to `nat`{.fact}.
    - ✅ By IHn we have `n0 = n0 + 0`{.claim}.
    - ✅ Applying f_equal_nat, we have `S n0 = S (n0 + 0)`{.claim}.
- ✅ These cases being exhaustive, we deduce `forall n0 : nat, n0 = n0 + 0`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- ✅ In particular `n = n + 0`{.claim}.
