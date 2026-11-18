---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# negb_andb

✅ Let `b1 b2 : bool`{.var}. We prove `negb (b1 && b2) = negb b1 || negb b2`{.claim}.

- ▫️ We prove `negb (b1 && b2) = negb b1 || negb b2`{.fact} by case analysis on `b2`{.fact} (bool, match):
- ✅ Case 1: we prove `negb (b1 && true) = negb b1 || negb true`{.claim}.
  - ▫️ We prove `negb (b1 && true) = negb b1 || negb true`{.fact} by case analysis on `b1`{.fact} (bool, match):
  - ✅ Case 1.1: we prove `negb (true && true) = negb true || negb true`{.claim}.
    - ✅ By definition of eq (eq_refl), we have `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ Case 1.2: we prove `negb (false && true) = negb false || negb true`{.claim}.
    - ✅ By definition of eq (eq_refl), we have `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ❌ These cases being exhaustive, we deduce `negb (b1 && true) = negb b1 || negb true`{.claim}.

    <details><summary>not proved: negb (b1 && true) = negb b1 || negb true</summary></details>

- ✅ Case 2: we prove `negb (b1 && false) = negb b1 || negb false`{.claim}.
  - ▫️ We prove `negb (b1 && false) = negb b1 || negb false`{.fact} by case analysis on `b1`{.fact} (bool, match):
  - ✅ Case 2.1: we prove `negb (true && false) = negb true || negb false`{.claim}.
    - ✅ By definition of eq (eq_refl), we have `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ Case 2.2: we prove `negb (false && false) = negb false || negb false`{.claim}.
    - ✅ By definition of eq (eq_refl), we have `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ These cases being exhaustive, we deduce `negb (b1 && false) = negb b1 || negb false`{.claim}.
- ❌ These cases being exhaustive, we deduce `negb (b1 && b2) = negb b1 || negb b2`{.claim}.

  <details><summary>not proved: negb (b1 && b2) = negb b1 || negb b2</summary></details>

