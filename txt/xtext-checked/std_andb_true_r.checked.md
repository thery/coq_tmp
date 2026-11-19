---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# andb_true_r

✅ Let `b : bool`{.var}. We prove `b && true = b`{.claim}.

- ✅ We prove `b && true = b` by case analysis on `b` (bool, match):
  - ✅ Case 1: we prove `true && true = true`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
  - ✅ Case 2: we prove `false && true = false`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.

  These cases being exhaustive, we deduce `b && true = b`{.claim}.
