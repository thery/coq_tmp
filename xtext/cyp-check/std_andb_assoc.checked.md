---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# andb_assoc

✅ Let `b1 b2 b3 : bool`{.var}. We prove `b1 && (b2 && b3) = b1 && b2 && b3`{.claim}.

- ✅ We prove `b1 && (b2 && b3) = b1 && b2 && b3` by case analysis on `b3` (bool, match):
  - ✅ Case 1: we prove `b1 && (b2 && true) = b1 && b2 && true`{.claim}.
    - ✅ We prove `b1 && (b2 && true) = b1 && b2 && true` by case analysis on `b2` (bool, match):
      - ✅ Case 1.1: we prove `b1 && (true && true) = b1 && true && true`{.claim}.
        - ✅ We prove `b1 && (true && true) = b1 && true && true` by case analysis on `b1` (bool, match):
          - ✅ Case 1.1.1: we prove `true && (true && true) = true && true && true`{.claim}.
            - ✅ By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
          - ✅ Case 1.1.2: we prove `false && (true && true) = false && true && true`{.claim}.
            - ✅ By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.

          These cases being exhaustive, we deduce `b1 && (true && true) = b1 && true && true`{.claim}.
      - ✅ Case 1.2: we prove `b1 && (false && true) = b1 && false && true`{.claim}.
        - ✅ We prove `b1 && (false && true) = b1 && false && true` by case analysis on `b1` (bool, match):
          - ✅ Case 1.2.1: we prove `true && (false && true) = true && false && true`{.claim}.
            - ✅ By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.
          - ✅ Case 1.2.2: we prove `false && (false && true) = false && false && true`{.claim}.
            - ✅ By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.

          These cases being exhaustive, we deduce `b1 && (false && true) = b1 && false && true`{.claim}.

      These cases being exhaustive, we deduce `b1 && (b2 && true) = b1 && b2 && true`{.claim}.
  - ✅ Case 2: we prove `b1 && (b2 && false) = b1 && b2 && false`{.claim}.
    - ✅ We prove `b1 && (b2 && false) = b1 && b2 && false` by case analysis on `b2` (bool, match):
      - ✅ Case 2.1: we prove `b1 && (true && false) = b1 && true && false`{.claim}.
        - ✅ We prove `b1 && (true && false) = b1 && true && false` by case analysis on `b1` (bool, match):
          - ✅ Case 2.1.1: we prove `true && (true && false) = true && true && false`{.claim}.
            - ✅ By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.
          - ✅ Case 2.1.2: we prove `false && (true && false) = false && true && false`{.claim}.
            - ✅ By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.

          These cases being exhaustive, we deduce `b1 && (true && false) = b1 && true && false`{.claim}.
      - ✅ Case 2.2: we prove `b1 && (false && false) = b1 && false && false`{.claim}.
        - ✅ We prove `b1 && (false && false) = b1 && false && false` by case analysis on `b1` (bool, match):
          - ✅ Case 2.2.1: we prove `true && (false && false) = true && false && false`{.claim}.
            - ✅ By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.
          - ✅ Case 2.2.2: we prove `false && (false && false) = false && false && false`{.claim}.
            - ✅ By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.

          These cases being exhaustive, we deduce `b1 && (false && false) = b1 && false && false`{.claim}.

      These cases being exhaustive, we deduce `b1 && (b2 && false) = b1 && b2 && false`{.claim}.

  These cases being exhaustive, we deduce `b1 && (b2 && b3) = b1 && b2 && b3`{.claim}.
