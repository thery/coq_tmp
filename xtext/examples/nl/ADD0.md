---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Laat `m : nat`{.var}. We bewijzen `m + 0 = m`{.claim}.

- Om te bewijzen `m + 0 = m`{.fact} met inductie (nat, nat_ind), veralgemenen we het tot `forall n : nat, n + 0 = n`{.fact}:
- Geval 1 (basis): we bewijzen `0 + 0 = 0 + 0`{.claim}.
  - Volgens de definitie van eq (eq_refl), er geldt `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Geval 2 (inductief): we bewijzen `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Kies willekeurig `m0 : nat`{.var}; stel volgens de inductiehypothese `m0 + 0 = m0`{.hyp} (IH).
    - Het element `nat`{.fact} behoort tot `Type`{.fact}.
    - Het element `nat`{.fact} behoort tot `Type`{.fact}.
    - Het element `S`{.fact} behoort tot `nat -> nat`{.fact}.
    - Het element `m0 + 0`{.fact} behoort tot `nat`{.fact}.
    - Het element `m0`{.fact} behoort tot `nat`{.fact}.
    - Volgens IH er geldt `m0 + 0 = m0`{.claim}.
    - Door toepassing van f_equal, er geldt `S (m0 + 0) = S m0`{.claim}.
- Deze gevallen zijn uitputtend, hieruit volgt `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- In het bijzonder `m + 0 = m`{.claim}.
