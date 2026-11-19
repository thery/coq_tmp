---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Laat `n : nat`{.var}. We bewijzen `n + 0 = n`{.claim}.

- We bewijzen `n + 0 = n`{.fact} met inductie naar `n`{.fact} (nat, nat_ind):
- Geval 1 (basis): we bewijzen `0 = 0`{.claim}.
  - Volgens de definitie van eq (eq_refl), er geldt `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Geval 2 (inductief): we bewijzen `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - Kies willekeurig `m : nat`{.var}; stel volgens de inductiehypothese `m + 0 = m`{.hyp} (IH).
    - Volgens de definitie van eq (eq_refl), er geldt `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Volgens IH er geldt `m + 0 = m`{.claim}.
    - Herschrijven met `m + 0 = m`{.fact} van rechts naar links (eq_ind_r), we krijgen `S (m + 0) = S m`{.claim}.
- Deze gevallen zijn uitputtend, hieruit volgt `n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
