---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: la
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Sit `b : bool`{.var}. Ostendamus `b = true \/ b = false`{.claim}.

- Ostendamus `b = true \/ b = false`{.fact} per casus in `b`{.fact} (bool, match):
- Casus 1: ostendamus `true = true \/ true = false`{.claim}.
  - Ex definitione eq (eq_refl), habemus `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Ex definitione or (or_introl), habemus `true = true \/ true = false`{.claim} *by Corelib.Init.Logic.or_introl*.
- Casus 2: ostendamus `false = true \/ false = false`{.claim}.
  - Ex definitione eq (eq_refl), habemus `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Ex definitione or (or_intror), habemus `false = true \/ false = false`{.claim} *by Corelib.Init.Logic.or_intror*.
- His casibus exhaustis, unde sequitur `b = true \/ b = false`{.claim}.
