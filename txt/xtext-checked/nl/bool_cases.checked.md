---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

✅ Laat `b : bool`{.var}. We bewijzen `b = true \/ b = false`{.claim}.

- ▫️ We bewijzen `b = true \/ b = false`{.fact} met gevalsonderscheiding naar `b`{.fact} (bool, match):
- ✅ Geval 1: we bewijzen `true = true \/ true = false`{.claim}.
  - ✅ Volgens de definitie van eq (eq_refl), er geldt `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ Volgens de definitie van or (or_introl), er geldt `true = true \/ true = false`{.claim} *by Corelib.Init.Logic.or_introl*.
- ✅ Geval 2: we bewijzen `false = true \/ false = false`{.claim}.
  - ✅ Volgens de definitie van eq (eq_refl), er geldt `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ Volgens de definitie van or (or_intror), er geldt `false = true \/ false = false`{.claim} *by Corelib.Init.Logic.or_intror*.
- ✅ Deze gevallen zijn uitputtend, hieruit volgt `b = true \/ b = false`{.claim}.
