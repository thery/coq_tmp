---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Let `b : bool`{.var}. We prove `b = true \/ b = false`{.claim}.

- We prove `b = true \/ b = false` by case analysis on *b*{.just} (*bool*{.just}, *match*{.just}):
  - Case 1: we prove `true = true \/ true = false`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
    - By definition of or (*or_introl*{.just}), we have `true = true \/ true = false`{.claim}.
  - Case 2: we prove `false = true \/ false = false`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.
    - By definition of or (*or_intror*{.just}), we have `false = true \/ false = false`{.claim}.

  These cases being exhaustive, we deduce `b = true \/ b = false`{.claim}.
