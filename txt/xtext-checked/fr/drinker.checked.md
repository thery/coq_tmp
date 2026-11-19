---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ Soit `A : Set`{.var}. Soit `P : A -> Prop`{.var}. Soit `y : A`{.var}. Montrons `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ En appliquant classic, nous avons `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ L'élément `forall z : A, P z`{.fact} appartient à `Prop`{.fact}.
- ▫️ Montrons `exists x : A, P x -> forall z : A, P z`{.fact} par analyse de cas sur `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- ✅ Cas 1: montrons `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Supposons `forall z : A, P z`{.hyp} (H).
    - ▫️ Supposons `P y`{.hyp} (_H).
      - ✅ Par H nous avons `forall z : A, P z`{.claim}.
    - ✅ Nous avons prouvé `P y -> forall z : A, P z`{.claim}.
    - ✅ Par définition de ex (ex_intro) avec le témoin `y`{.fact}, nous avons `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Cas 2: montrons `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Supposons `~ (forall z : A, P z)`{.hyp} (H).
    - ❌ En appliquant not_all_ex_not à A, P et H, nous avons `exists n : A, ~ P n`{.claim} (e).

      <details><summary>non démontré : exists n : A, ~ P n</summary></details>

    - ✅ En revenant à la définition de ex (match) dans `exists n : A, ~ P n`{.fact} (e), montrons `exists x : A, P x -> forall z : A, P z`{.claim}:
      - ▫️ Choisissons arbitrairement `t : A`{.var}; supposons `~ P t`{.hyp} (i).
        - ▫️ Supposons `P t`{.hyp} (h).
          - ✅ Par application, avec h, nous avons `False`{.claim} (f).
            - ✅ Par i nous avons `~ P t`{.claim}, c'est-à-dire `P t -> False`{.fact}.
          - ✅ Par contradiction (False, match), à partir de `False`{.fact} (f) nous pouvons déduire `forall z : A, P z`{.claim}.
        - ✅ Nous avons prouvé `P t -> forall z : A, P z`{.claim}.
        - ✅ Par définition de ex (ex_intro) avec le témoin `t`{.fact}, nous avons `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Nous avons `exists x : A, P x -> forall z : A, P z`{.claim} dans tous les cas.
