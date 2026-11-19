---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Laat `x y z t : Prop`{.var}. Stel `(x -> z) /\ (y -> t)`{.hyp} (h1) en `x /\ y`{.hyp} (h2). We bewijzen `z /\ t`{.claim}.

- Terug naar de definitie van and (and_ind) in `(x -> z) /\ (y -> t)`{.fact} (h1), we bewijzen `z /\ t`{.claim}:
  - Stel `x -> z`{.hyp} (i) en `y -> t`{.hyp} (j).
    - Terug naar de definitie van and (and_ind) in `x /\ y`{.fact} (h2), we bewijzen `z /\ t`{.claim}:
      - Stel `x`{.hyp} (k) en `y`{.hyp} (l).
        - Door toepassing van i op k, er geldt `z`{.claim}.
        - Door toepassing van j op l, er geldt `t`{.claim}.
        - Dus volgens de definitie van and (conj), er geldt `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
