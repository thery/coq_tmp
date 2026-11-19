---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ Laat `A : Set`{.var}. Laat `P : A -> Prop`{.var}. Laat `y : A`{.var}. We bewijzen `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ Door toepassing van classic, er geldt `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ Het element `forall z : A, P z`{.fact} behoort tot `Prop`{.fact}.
- ▫️ We bewijzen `exists x : A, P x -> forall z : A, P z`{.fact} met gevalsonderscheiding naar `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- ✅ Geval 1: we bewijzen `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Stel `forall z : A, P z`{.hyp} (H).
    - ▫️ Stel `P y`{.hyp} (_H).
      - ✅ Volgens H er geldt `forall z : A, P z`{.claim}.
    - ✅ We hebben bewezen `P y -> forall z : A, P z`{.claim}.
    - ✅ Volgens de definitie van ex (ex_intro) met getuige `y`{.fact}, er geldt `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Geval 2: we bewijzen `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Stel `~ (forall z : A, P z)`{.hyp} (H).
    - ❌ Door toepassing van not_all_ex_not op A, P en H, er geldt `exists n : A, ~ P n`{.claim} (e).

      <details><summary>not proved: exists n : A, ~ P n</summary></details>

    - ✅ Terug naar de definitie van ex (match) in `exists n : A, ~ P n`{.fact} (e), we bewijzen `exists x : A, P x -> forall z : A, P z`{.claim}:
      - ▫️ Kies willekeurig `t : A`{.var}; stel `~ P t`{.hyp} (i).
        - ▫️ Stel `P t`{.hyp} (h).
          - ✅ Door toepassing, met h, er geldt `False`{.claim} (f).
            - ✅ Volgens i er geldt `~ P t`{.claim}, dat wil zeggen `P t -> False`{.fact}.
          - ✅ Uit het ongerijmde (False, match), uit `False`{.fact} (f) kunnen we afleiden `forall z : A, P z`{.claim}.
        - ✅ We hebben bewezen `P t -> forall z : A, P z`{.claim}.
        - ✅ Volgens de definitie van ex (ex_intro) met getuige `t`{.fact}, er geldt `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Er geldt `exists x : A, P x -> forall z : A, P z`{.claim} in alle gevallen.
