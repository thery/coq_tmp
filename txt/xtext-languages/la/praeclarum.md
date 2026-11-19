---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Sint `x y z t : Prop`{.var}. Ponamus `(x -> z) /\ (y -> t)`{.hyp} (h1) et `x /\ y`{.hyp} (h2). Ostendamus `z /\ t`{.claim}.

- Redeuntes ad definitionem and (*and_ind*{.just}) in *h1*{.just}, ostendamus `z /\ t`{.claim}:
  - Ponamus `x -> z`{.hyp} (i) et `y -> t`{.hyp} (j). Redeuntes ad definitionem and (*and_ind*{.just}) in *h2*{.just}, ostendamus `z /\ t`{.claim}:
    - Ponamus `x`{.hyp} (k) et `y`{.hyp} (l).
      - Applicando *i*{.just} ad *k*{.just}, habemus `z`{.claim}.
      - Applicando *j*{.just} ad *l*{.just}, habemus `t`{.claim}.

      Ergo ex definitione and (*conj*{.just}), habemus `z /\ t`{.claim}.
