---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# orb_false_r

✅ Let `b : bool`{.var}. We prove `b || false = b`{.claim}.

- ▫️ We prove `b || false = b`{.fact} by case analysis on `b`{.fact} (bool, match):
- ✅ Case 1: we prove `true || false = true`{.claim}.
  - ✅ By definition of eq (eq_refl), we have `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Case 2: we prove `false || false = false`{.claim}.
  - ✅ By definition of eq (eq_refl), we have `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ These cases being exhaustive, we deduce `b || false = b`{.claim}.
