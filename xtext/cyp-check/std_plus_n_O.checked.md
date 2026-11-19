---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_O

✅ Let `n : nat`{.var}. We prove `n = n + 0`{.claim}.

- ✅ We prove `n = n + 0` by induction on *n*{.just} (*nat*{.just}, *induction*{.just}):
  - ✅ Case 1 (base): we prove `0 = 0 + 0`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `0 = 0`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall n0 : nat, n0 = n0 + 0 -> S n0 = S n0 + 0`{.claim}.
    - ✅ Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `n0 = n0 + 0`{.hyp} (IHn).
      - ▫️ The element `nat` belongs to `Type`.
      - ▫️ The element `S` belongs to `nat -> nat`.
      - ▫️ The element `n0 + 0` belongs to `nat`.
      - ✅ By *IHn*{.just} we have `n0 = n0 + 0`{.claim}.

      Applying *f_equal_nat*{.just}, we have `S n0 = S (n0 + 0)`{.claim}.

  These cases being exhaustive, we deduce `n = n + 0`{.claim}.
