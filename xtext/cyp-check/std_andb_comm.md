---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# andb_comm

Let `b1 b2 : bool`{.var}. We prove `b1 && b2 = b2 && b1`{.claim}.

- We prove `b1 && b2 = b2 && b1` by case analysis on `b2` (bool, match):
  - Case 1: we prove `b1 && true = true && b1`{.claim}.
    - We prove `b1 && true = true && b1` by case analysis on `b1` (bool, match):
      - Case 1.1: we prove `true && true = true && true`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
      - Case 1.2: we prove `false && true = true && false`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.

      These cases being exhaustive, we deduce `b1 && true = true && b1`{.claim}.
  - Case 2: we prove `b1 && false = false && b1`{.claim}.
    - We prove `b1 && false = false && b1` by case analysis on `b1` (bool, match):
      - Case 2.1: we prove `true && false = false && true`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.
      - Case 2.2: we prove `false && false = false && false`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.

      These cases being exhaustive, we deduce `b1 && false = false && b1`{.claim}.

  These cases being exhaustive, we deduce `b1 && b2 = b2 && b1`{.claim}.
