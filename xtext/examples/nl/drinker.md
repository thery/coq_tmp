---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Laat `A : Set`{.var}. Laat `P : A -> Prop`{.var}. Laat `y : A`{.var}. We bewijzen `exists x : A, P x -> forall z : A, P z`{.claim}.

- Door toepassing van *Classical_Prop.classic*{.just}, er geldt `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Het element `forall z : A, P z` behoort tot `Prop`.
- We bewijzen `exists x : A, P x -> forall z : A, P z` met gevalsonderscheiding naar *o*{.just} (*or*{.just}, *match*{.just}):
  - Geval 1: we bewijzen `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Stel `forall z : A, P z`{.hyp} (H).
      - Stel `P y`{.hyp} (_H). Volgens *H*{.just} er geldt `forall z : A, P z`{.claim}.
      - We hebben bewezen `P y -> forall z : A, P z`{.claim}.

      Volgens de definitie van ex (*ex_intro*{.just}) met getuige `y`, er geldt `exists x : A, P x -> forall z : A, P z`{.claim}.
  - Geval 2: we bewijzen `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Stel `~ (forall z : A, P z)`{.hyp} (H).
      - Door toepassing van *Classical_Pred_Type.not_all_ex_not*{.just} op A, P en *H*{.just}, er geldt `exists n : A, ~ P n`{.claim} (e).
      - Terug naar de definitie van *ex*{.just} (*match*{.just}) in *e*{.just}, we bewijzen `exists x : A, P x -> forall z : A, P z`{.claim}:
        - Kies willekeurig `t : A`{.var}; stel `~ P t`{.hyp} (i).
          - Stel `P t`{.hyp} (h).
            - Door toepassing, met *h*{.just}, er geldt `False`{.claim} (f).
              - Volgens *i*{.just} er geldt `~ P t`, dat wil zeggen `P t -> False`{.claim}.

            Uit het ongerijmde (*False*{.just}, *match*{.just}), uit *f*{.just} kunnen we afleiden `forall z : A, P z`{.claim}.
          - We hebben bewezen `P t -> forall z : A, P z`{.claim}.

          Volgens de definitie van ex (*ex_intro*{.just}) met getuige `t`, er geldt `exists x : A, P x -> forall z : A, P z`{.claim}.

      Er geldt `exists x : A, P x -> forall z : A, P z`{.claim}.

  Er geldt `exists x : A, P x -> forall z : A, P z`{.claim} in alle gevallen.
