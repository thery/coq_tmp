---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Sint `x y z t : Prop`{.var}. Ponamus `(x -> z) /\ (y -> t)`{.hyp} (h1) et `x /\ y`{.hyp} (h2). Ostendamus `z /\ t`{.claim}.

- Redeuntes ad definitionem and (and_ind) in `(x -> z) /\ (y -> t)`{.fact} (h1), ostendamus `z /\ t`{.claim}:
  - Ponamus `x -> z`{.hyp} (i) et `y -> t`{.hyp} (j).
    - Redeuntes ad definitionem and (and_ind) in `x /\ y`{.fact} (h2), ostendamus `z /\ t`{.claim}:
      - Ponamus `x`{.hyp} (k) et `y`{.hyp} (l).
        - Applicando i ad k, habemus `z`{.claim}.
        - Applicando j ad l, habemus `t`{.claim}.
        - Ergo ex definitione and (conj), habemus `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
