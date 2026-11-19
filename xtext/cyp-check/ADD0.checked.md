---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Let `m : nat`{.var}. We prove `m + 0 = m`{.claim}.

- ✅ We prove `m + 0 = m` by induction on `m` (nat, *nat_ind*{.just}):
  - ✅ Case 1 (base): we prove `0 + 0 = 0 + 0`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `0 + 0 = 0 + 0`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - ✅ Let us choose arbitrarily `m0 : nat`{.var}; assume by induction hypothesis `m0 + 0 = m0`{.hyp} (IH).
      - ▫️ The element `nat` belongs to `Type`.
      - ▫️ The element `nat` belongs to `Type`.
      - ▫️ The element `S` belongs to `nat -> nat`.
      - ▫️ The element `m0 + 0` belongs to `nat`.
      - ✅ By *IH*{.just} we have `m0 + 0 = m0`{.claim}.

      Applying *f_equal*{.just}, we have `S (m0 + 0) = S m0`{.claim}.

  These cases being exhaustive, we deduce `m + 0 = m`{.claim}.
