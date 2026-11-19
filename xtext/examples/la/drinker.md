---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Sit `A : Set`{.var}. Sit `P : A -> Prop`{.var}. Sit `y : A`{.var}. Ostendamus `exists x : A, P x -> forall z : A, P z`{.claim}.

- Applicando *Classical_Prop.classic*{.just}, habemus `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Elementum `forall z : A, P z` pertinet ad `Prop`.
- Ostendamus `exists x : A, P x -> forall z : A, P z` per casus in *o*{.just} (or, match):
  - Casus 1: ostendamus `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Ponamus `forall z : A, P z`{.hyp} (H).
      - Ponamus `P y`{.hyp} (_H). Per *H*{.just} habemus `forall z : A, P z`{.claim}.
      - Ostendimus `P y -> forall z : A, P z`{.claim}.

      Ex definitione ex (*ex_intro*{.just}) cum teste `y`, habemus `exists x : A, P x -> forall z : A, P z`{.claim}.
  - Casus 2: ostendamus `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Ponamus `~ (forall z : A, P z)`{.hyp} (H).
      - Applicando *Classical_Pred_Type.not_all_ex_not*{.just} ad A, P et *H*{.just}, habemus `exists n : A, ~ P n`{.claim} (e).
      - Redeuntes ad definitionem ex (match) in *e*{.just}, ostendamus `exists x : A, P x -> forall z : A, P z`{.claim}:
        - Eligamus quaelibet `t : A`{.var}; ponamus `~ P t`{.hyp} (i).
          - Ponamus `P t`{.hyp} (h).
            - Per applicationem, cum *h*{.just}, habemus `False`{.claim} (f).
              - Per *i*{.just} habemus `~ P t`, id est `P t -> False`{.claim}.

            Per absurdum (False, match), ex *f*{.just} deducere possumus `forall z : A, P z`{.claim}.
          - Ostendimus `P t -> forall z : A, P z`{.claim}.

          Ex definitione ex (*ex_intro*{.just}) cum teste `t`, habemus `exists x : A, P x -> forall z : A, P z`{.claim}.

      Habemus `exists x : A, P x -> forall z : A, P z`{.claim}.

  Habemus `exists x : A, P x -> forall z : A, P z`{.claim} in omnibus casibus.
