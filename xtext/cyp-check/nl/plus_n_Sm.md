---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: nl
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

Laat `n m : nat`{.var}. We bewijzen `S (n + m) = n + S m`{.claim}.

- We bewijzen `S (n + m) = n + S m`{.fact} met inductie naar `n`{.fact} (nat, nat_ind):
- Geval 1 (basis): we bewijzen `0 + S m = 0 + S m`{.claim}.
  - Volgens de definitie van eq (eq_refl), er geldt `0 + S m = 0 + S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Geval 2 (inductief): we bewijzen `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
  - Kies willekeurig `n0 : nat`{.var}; stel volgens de inductiehypothese `S (n0 + m) = n0 + S m`{.hyp} (IH).
    - Volgens de definitie van eq (eq_refl), er geldt `S (n0 + S m) = S (n0 + S m)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Volgens IH er geldt `S (n0 + m) = n0 + S m`{.claim}.
    - Herschrijven met `S (n0 + m) = n0 + S m`{.fact} van rechts naar links (eq_ind_r), we krijgen `S (S (n0 + m)) = S (n0 + S m)`{.claim}.
- Deze gevallen zijn uitputtend, hieruit volgt `S (n + m) = n + S m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
