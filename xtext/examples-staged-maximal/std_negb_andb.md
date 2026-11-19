---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# negb_andb

Let `b1 b2 : bool`{.var}. We prove `negb (b1 && b2) = negb b1 || negb b2`{.claim}.

- We prove `negb (b1 && b2) = negb b1 || negb b2` by case analysis on `b2` (bool, match):
  - Case 1: we prove `negb (b1 && true) = negb b1 || negb true`{.claim}.
    - We prove `negb (b1 && true) = negb b1 || negb true` by case analysis on `b1` (bool, match):
      - Case 1.1: we prove `negb (true && true) = negb true || negb true`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `false = false`{.claim}.
      - Case 1.2: we prove `negb (false && true) = negb false || negb true`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.

      These cases being exhaustive, we deduce `negb (b1 && true) = negb b1 || negb true`{.claim}.
  - Case 2: we prove `negb (b1 && false) = negb b1 || negb false`{.claim}.
    - We prove `negb (b1 && false) = negb b1 || negb false` by case analysis on `b1` (bool, match):
      - Case 2.1: we prove `negb (true && false) = negb true || negb false`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
      - Case 2.2: we prove `negb (false && false) = negb false || negb false`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.

      These cases being exhaustive, we deduce `negb (b1 && false) = negb b1 || negb false`{.claim}.

  These cases being exhaustive, we deduce `negb (b1 && b2) = negb b1 || negb b2`{.claim}.
