---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

✅ Laat `b : bool`{.var}. We bewijzen `b = true \/ b = false`{.claim}.

- ✅ We bewijzen `b = true \/ b = false` met gevalsonderscheiding naar *b*{.just} (*bool*{.just}, *match*{.just}):
  - ✅ Geval 1: we bewijzen `true = true \/ true = false`{.claim}.
    - ✅ Volgens de definitie van eq (*eq_refl*{.just}), er geldt `true = true`{.claim}.
    - ✅ Volgens de definitie van or (*or_introl*{.just}), er geldt `true = true \/ true = false`{.claim}.
  - ✅ Geval 2: we bewijzen `false = true \/ false = false`{.claim}.
    - ✅ Volgens de definitie van eq (*eq_refl*{.just}), er geldt `false = false`{.claim}.
    - ✅ Volgens de definitie van or (*or_intror*{.just}), er geldt `false = true \/ false = false`{.claim}.

  Deze gevallen zijn uitputtend, hieruit volgt `b = true \/ b = false`{.claim}.
