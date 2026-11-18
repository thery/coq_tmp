---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Sint `x y z t : Prop`{.var}. Ponamus `(x -> z) /\ (y -> t)`{.hyp} (h1) et `x /\ y`{.hyp} (h2). Ostendamus `z /\ t`{.claim}.

- Redeuntes ad definitionem and (and_ind) in `(x -> z) /\ (y -> t)`{.fact} (h1), ostendamus `z /\ t`{.claim}:
  - Ponamus `x -> z`{.hyp} (i) et `y -> t`{.hyp} (j).
    - Redeuntes ad definitionem and (and_ind) in `x /\ y`{.fact} (h2), ostendamus `z /\ t`{.claim}:
      - Ponamus `x`{.hyp} (k) et `y`{.hyp} (l).
        - Unde sequitur `z`{.claim}.
          - Per k habemus `x`{.claim}.
          - Per i habemus `x -> z`{.claim}.
        - Unde sequitur `t`{.claim}.
          - Per l habemus `y`{.claim}.
          - Per j habemus `y -> t`{.claim}.
        - Ergo ex definitione and (conj), habemus `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
