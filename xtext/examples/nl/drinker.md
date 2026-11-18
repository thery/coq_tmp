---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Laat `A : Set`{.var}. Laat `P : A -> Prop`{.var}. Laat `y : A`{.var}. We bewijzen `exists x : A, P x -> forall z : A, P z`{.claim}.

- In het bijzonder `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Met behulp van classic we krijgen `forall P0 : Prop, P0 \/ ~ P0`{.claim} *by Stdlib.Logic.Classical_Prop.classic*.
- We bewijzen `exists x : A, P x -> forall z : A, P z`{.fact} met gevalsonderscheiding naar `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- Geval 1: we bewijzen `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Stel `forall z : A, P z`{.hyp} (H).
    - Stel `P y`{.hyp} (_H).
      - Volgens H er geldt `forall z : A, P z`{.claim}.
    - We hebben bewezen `P y -> forall z : A, P z`{.claim}.
    - Volgens de definitie van ex (ex_intro) met getuige `y`{.fact}, er geldt `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Geval 2: we bewijzen `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Stel `~ (forall z : A, P z)`{.hyp} (H).
    - Hieruit volgt `exists n : A, ~ P n`{.claim} (e).
      - Volgens H er geldt `~ (forall z : A, P z)`{.claim}.
      - Met behulp van not_all_ex_not we krijgen `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - Terug naar de definitie van ex (match) in `exists n : A, ~ P n`{.fact} (e), we bewijzen `exists x : A, P x -> forall z : A, P z`{.claim}:
      - Beschouw een willekeurige `t : A`{.var}.
        - Stel `~ P t`{.hyp} (i).
          - Stel `P t`{.hyp} (h).
            - Hieruit volgt `False`{.claim} (f).
              - Volgens h er geldt `P t`{.claim}.
              - Volgens i er geldt `~ P t`{.claim}, dat wil zeggen `P t -> False`{.fact}.
            - Uit het ongerijmde (False, match), uit `False`{.fact} (f) kunnen we afleiden `forall z : A, P z`{.claim}.
          - We hebben bewezen `P t -> forall z : A, P z`{.claim}.
          - Volgens de definitie van ex (ex_intro) met getuige `t`{.fact}, er geldt `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Er geldt `exists x : A, P x -> forall z : A, P z`{.claim} in alle gevallen.
