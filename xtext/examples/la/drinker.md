---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Sit `A : Set`{.var}. Sit `P : A -> Prop`{.var}. Sit `y : A`{.var}. Ostendamus `exists x : A, P x -> forall z : A, P z`{.claim}.

- Speciatim `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Adhibentes classic obtinemus `forall P0 : Prop, P0 \/ ~ P0`{.claim} *by Stdlib.Logic.Classical_Prop.classic*.
- Ostendamus `exists x : A, P x -> forall z : A, P z`{.fact} per casus in `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- Casus 1: ostendamus `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Ponamus `forall z : A, P z`{.hyp} (H).
    - Ponamus `P y`{.hyp} (_H).
      - Per H habemus `forall z : A, P z`{.claim}.
    - Ostendimus `P y -> forall z : A, P z`{.claim}.
    - Ex definitione ex (ex_intro) cum teste `y`{.fact}, habemus `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Casus 2: ostendamus `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Ponamus `~ (forall z : A, P z)`{.hyp} (H).
    - Unde sequitur `exists n : A, ~ P n`{.claim} (e).
      - Per H habemus `~ (forall z : A, P z)`{.claim}.
      - Adhibentes not_all_ex_not obtinemus `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - Redeuntes ad definitionem ex (match) in `exists n : A, ~ P n`{.fact} (e), ostendamus `exists x : A, P x -> forall z : A, P z`{.claim}:
      - Consideremus quodlibet `t : A`{.var}.
        - Ponamus `~ P t`{.hyp} (i).
          - Ponamus `P t`{.hyp} (h).
            - Unde sequitur `False`{.claim} (f).
              - Per h habemus `P t`{.claim}.
              - Per i habemus `~ P t`{.claim}, id est `P t -> False`{.fact}.
            - Per absurdum (False, match), ex `False`{.fact} (f) deducere possumus `forall z : A, P z`{.claim}.
          - Ostendimus `P t -> forall z : A, P z`{.claim}.
          - Ex definitione ex (ex_intro) cum teste `t`{.fact}, habemus `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Habemus `exists x : A, P x -> forall z : A, P z`{.claim} in omnibus casibus.
