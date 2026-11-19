---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: nl
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

Laat `n m : nat`{.var}. Stel `n <= m`{.hyp} (H). We bewijzen `S n <= S m`{.claim}.

- We bewijzen `S n <= S m` met inductie naar *H*{.just} (*le*{.just}, *induction*{.just}):
  - Geval 1 (basis): we bewijzen `S n <= S n`{.claim}.
    - Volgens de definitie van le (*le_n*{.just}), er geldt `S n <= S n`{.claim}.
  - Geval 2 (inductief): we bewijzen `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
    - Kies willekeurig `m0 : nat`{.var}; stel `n <= m0`{.hyp} (H0) en volgens de inductiehypothese `S n <= S m0`{.hyp} (IH). Volgens de definitie van le (*le_S*{.just}) met getuige `S m0`, uit *IH*{.just} hieruit volgt `S n <= S (S m0)`{.claim}.

  Er geldt `S n <= S m`{.claim} in alle gevallen.
