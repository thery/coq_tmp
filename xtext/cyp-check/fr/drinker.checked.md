---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ Soit `A : Set`{.var}. Soit `P : A -> Prop`{.var}. Soit `y : A`{.var}. Montrons `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ En appliquant *Classical_Prop.classic*{.just}, nous avons `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ L'élément `forall z : A, P z` appartient à `Prop`.
- ✅ Montrons `exists x : A, P x -> forall z : A, P z` par analyse de cas sur *o*{.just} (or, match):
  - ✅ Cas 1: montrons `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - ✅ Supposons `forall z : A, P z`{.hyp} (H).
      - ✅ Supposons `P y`{.hyp} (_H). Par *H*{.just} nous avons `forall z : A, P z`{.claim}.
      - ✅ Nous avons prouvé `P y -> forall z : A, P z`{.claim}.

      Par définition de ex (*ex_intro*{.just}) avec le témoin `y`, nous avons `exists x : A, P x -> forall z : A, P z`{.claim}.
  - ✅ Cas 2: montrons `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - ✅ Supposons `~ (forall z : A, P z)`{.hyp} (H).
      - ✅ En appliquant *Classical_Pred_Type.not_all_ex_not*{.just} à A, P et *H*{.just}, nous avons `exists n : A, ~ P n`{.claim} (e).
      - ✅ En revenant à la définition de ex (match) dans *e*{.just}, montrons `exists x : A, P x -> forall z : A, P z`{.claim}:
        - ✅ Choisissons arbitrairement `t : A`{.var}; supposons `~ P t`{.hyp} (i).
          - ✅ Supposons `P t`{.hyp} (h).
            - ✅ Par application, avec *h*{.just}, nous avons `False`{.claim} (f).
              - ✅ Par *i*{.just} nous avons `~ P t`, c'est-à-dire `P t -> False`{.claim}.

            Par contradiction (False, match), à partir de *f*{.just} nous pouvons déduire `forall z : A, P z`{.claim}.
          - ✅ Nous avons prouvé `P t -> forall z : A, P z`{.claim}.

          Par définition de ex (*ex_intro*{.just}) avec le témoin `t`, nous avons `exists x : A, P x -> forall z : A, P z`{.claim}.

      Nous avons `exists x : A, P x -> forall z : A, P z`{.claim}.

  Nous avons `exists x : A, P x -> forall z : A, P z`{.claim} dans tous les cas.
