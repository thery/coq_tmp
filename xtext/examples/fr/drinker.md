---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Soit `A : Set`{.var}. Soit `P : A -> Prop`{.var}. Soit `y : A`{.var}. Montrons `exists x : A, P x -> forall z : A, P z`{.claim}.

- En particulier `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - En utilisant classic nous obtenons `forall P0 : Prop, P0 \/ ~ P0`{.claim} *by Stdlib.Logic.Classical_Prop.classic*.
- Montrons `exists x : A, P x -> forall z : A, P z`{.fact} par analyse de cas sur `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- Cas 1: montrons `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Supposons `forall z : A, P z`{.hyp} (H).
    - Supposons `P y`{.hyp} (_H).
      - Par H nous avons `forall z : A, P z`{.claim}.
    - Nous avons prouvé `P y -> forall z : A, P z`{.claim}.
    - Par définition de ex (ex_intro) avec le témoin `y`{.fact}, nous avons `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Cas 2: montrons `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Supposons `~ (forall z : A, P z)`{.hyp} (H).
    - Nous en déduisons `exists n : A, ~ P n`{.claim} (e).
      - Par H nous avons `~ (forall z : A, P z)`{.claim}.
      - En utilisant not_all_ex_not nous obtenons `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - En revenant à la définition de ex (match) dans `exists n : A, ~ P n`{.fact} (e), montrons `exists x : A, P x -> forall z : A, P z`{.claim}:
      - Considérons un élément arbitraire `t : A`{.var}.
        - Supposons `~ P t`{.hyp} (i).
          - Supposons `P t`{.hyp} (h).
            - Nous en déduisons `False`{.claim} (f).
              - Par h nous avons `P t`{.claim}.
              - Par i nous avons `~ P t`{.claim}, c'est-à-dire `P t -> False`{.fact}.
            - Par contradiction (False, match), à partir de `False`{.fact} (f) nous pouvons déduire `forall z : A, P z`{.claim}.
          - Nous avons prouvé `P t -> forall z : A, P z`{.claim}.
          - Par définition de ex (ex_intro) avec le témoin `t`{.fact}, nous avons `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Nous avons `exists x : A, P x -> forall z : A, P z`{.claim} dans tous les cas.
