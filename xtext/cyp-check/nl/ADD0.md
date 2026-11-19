---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: nl
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Laat `m : nat`{.var}. We bewijzen `m + 0 = m`{.claim}.

- We bewijzen `m + 0 = m` met inductie naar `m` (nat, *nat_ind*{.just}):
  - Geval 1 (basis): we bewijzen `0 + 0 = 0 + 0`{.claim}.
    - Volgens de definitie van eq (*eq_refl*{.just}), er geldt `0 + 0 = 0 + 0`{.claim}.
  - Geval 2 (inductief): we bewijzen `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - Kies willekeurig `m0 : nat`{.var}; stel volgens de inductiehypothese `m0 + 0 = m0`{.hyp} (IH).
      - Het element `nat` behoort tot `Type`.
      - Het element `nat` behoort tot `Type`.
      - Het element `S` behoort tot `nat -> nat`.
      - Het element `m0 + 0` behoort tot `nat`.
      - Volgens *IH*{.just} er geldt `m0 + 0 = m0`{.claim}.

      Door toepassing van *f_equal*{.just}, er geldt `S (m0 + 0) = S m0`{.claim}.

  Deze gevallen zijn uitputtend, hieruit volgt `m + 0 = m`{.claim}.
