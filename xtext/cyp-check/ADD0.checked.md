---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Let `m : nat`{.var}. We prove `m + 0 = m`{.claim}.

- ▫️ We prove `m + 0 = m`{.fact} by induction on `m`{.fact} (nat, nat_ind):
- ✅ Case 1 (base): we prove `0 + 0 = 0 + 0`{.claim}.
  - ✅ By definition of eq (eq_refl), we have `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Case 2 (inductive): we prove `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - ▫️ Let us choose arbitrarily `m0 : nat`{.var}; assume by induction hypothesis `m0 + 0 = m0`{.hyp} (IH).
    - ▫️ The element `nat`{.fact} belongs to `Type`{.fact}.
    - ▫️ The element `nat`{.fact} belongs to `Type`{.fact}.
    - ▫️ The element `S`{.fact} belongs to `nat -> nat`{.fact}.
    - ▫️ The element `m0 + 0`{.fact} belongs to `nat`{.fact}.
    - ▫️ The element `m0`{.fact} belongs to `nat`{.fact}.
    - ✅ By IH we have `m0 + 0 = m0`{.claim}.
    - ✅ Applying f_equal, we have `S (m0 + 0) = S m0`{.claim}.
- ✅ These cases being exhaustive, we deduce `m + 0 = m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
