---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# orb_false_r

Let `b : bool`{.var}. We prove `b || false = b`{.claim}.

- We prove `b || false = b` by case analysis on *b*{.just} (*bool*{.just}, *match*{.just}):
  - Case 1: we prove `true || false = true`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
  - Case 2: we prove `false || false = false`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.

  These cases being exhaustive, we deduce `b || false = b`{.claim}.
