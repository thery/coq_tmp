---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

Laat `n m : nat`{.var}. We bewijzen `S (n + m) = n + S m`{.claim}.

- We bewijzen `S (n + m) = n + S m` met inductie naar *n*{.just} (*nat*{.just}, *induction*{.just}):
  - Geval 1 (basis): we bewijzen `0 + S m = 0 + S m`{.claim}.
    - Volgens de definitie van eq (*eq_refl*{.just}), er geldt `0 + S m = 0 + S m`{.claim}.
  - Geval 2 (inductief): we bewijzen `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
    - Kies willekeurig `n0 : nat`{.var}; stel volgens de inductiehypothese `S (n0 + m) = n0 + S m`{.hyp} (IH).
      - Volgens de definitie van eq (*eq_refl*{.just}), er geldt `S (n0 + S m) = S (n0 + S m)`{.claim}.
      - Volgens *IH*{.just} er geldt `S (n0 + m) = n0 + S m`{.claim}.

      Herschrijven met `S (n0 + m) = n0 + S m`{.fact} van rechts naar links (eq_ind_r), we krijgen `S (S (n0 + m)) = S (n0 + S m)`{.claim}.

  Deze gevallen zijn uitputtend, hieruit volgt `S (n + m) = n + S m`{.claim}.
