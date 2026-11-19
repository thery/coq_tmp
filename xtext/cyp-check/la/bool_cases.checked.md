---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: la
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

✅ Sit `b : bool`{.var}. Ostendamus `b = true \/ b = false`{.claim}.

- ✅ Ostendamus `b = true \/ b = false` per casus in `b` (bool, match):
  - ✅ Casus 1: ostendamus `true = true \/ true = false`{.claim}.
    - ✅ Ex definitione eq (*eq_refl*{.just}), habemus `true = true`{.claim}.
    - ✅ Ex definitione or (*or_introl*{.just}), habemus `true = true \/ true = false`{.claim}.
  - ✅ Casus 2: ostendamus `false = true \/ false = false`{.claim}.
    - ✅ Ex definitione eq (*eq_refl*{.just}), habemus `false = false`{.claim}.
    - ✅ Ex definitione or (*or_intror*{.just}), habemus `false = true \/ false = false`{.claim}.

  His casibus exhaustis, unde sequitur `b = true \/ b = false`{.claim}.
