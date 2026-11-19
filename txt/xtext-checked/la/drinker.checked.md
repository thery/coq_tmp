---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ Sit `A : Set`{.var}. Sit `P : A -> Prop`{.var}. Sit `y : A`{.var}. Ostendamus `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ Applicando classic, habemus `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ Elementum `forall z : A, P z`{.fact} pertinet ad `Prop`{.fact}.
- ▫️ Ostendamus `exists x : A, P x -> forall z : A, P z`{.fact} per casus in `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- ✅ Casus 1: ostendamus `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Ponamus `forall z : A, P z`{.hyp} (H).
    - ▫️ Ponamus `P y`{.hyp} (_H).
      - ✅ Per H habemus `forall z : A, P z`{.claim}.
    - ✅ Ostendimus `P y -> forall z : A, P z`{.claim}.
    - ✅ Ex definitione ex (ex_intro) cum teste `y`{.fact}, habemus `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Casus 2: ostendamus `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Ponamus `~ (forall z : A, P z)`{.hyp} (H).
    - ❌ Applicando not_all_ex_not ad A, P et H, habemus `exists n : A, ~ P n`{.claim} (e).

      <details><summary>not proved: exists n : A, ~ P n</summary></details>

    - ✅ Redeuntes ad definitionem ex (match) in `exists n : A, ~ P n`{.fact} (e), ostendamus `exists x : A, P x -> forall z : A, P z`{.claim}:
      - ▫️ Eligamus quaelibet `t : A`{.var}; ponamus `~ P t`{.hyp} (i).
        - ▫️ Ponamus `P t`{.hyp} (h).
          - ✅ Per applicationem, cum h, habemus `False`{.claim} (f).
            - ✅ Per i habemus `~ P t`{.claim}, id est `P t -> False`{.fact}.
          - ✅ Per absurdum (False, match), ex `False`{.fact} (f) deducere possumus `forall z : A, P z`{.claim}.
        - ✅ Ostendimus `P t -> forall z : A, P z`{.claim}.
        - ✅ Ex definitione ex (ex_intro) cum teste `t`{.fact}, habemus `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Habemus `exists x : A, P x -> forall z : A, P z`{.claim} in omnibus casibus.
