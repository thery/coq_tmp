---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ Sia `A : Set`{.var}. Sia `P : A -> Prop`{.var}. Sia `y : A`{.var}. Dimostriamo `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ In particolare `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ✅ Usando classic otteniamo `forall P0 : Prop, P0 \/ ~ P0`{.claim} *by Stdlib.Logic.Classical_Prop.classic*.
- ▫️ Dimostriamo `exists x : A, P x -> forall z : A, P z`{.fact} per casi su `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- ✅ Caso 1: dimostriamo `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Supponiamo `forall z : A, P z`{.hyp} (H).
    - ▫️ Supponiamo `P y`{.hyp} (_H).
      - ✅ Per H abbiamo `forall z : A, P z`{.claim}.
    - ✅ Abbiamo dimostrato `P y -> forall z : A, P z`{.claim}.
    - ✅ Per definizione di ex (ex_intro) con testimone `y`{.fact}, abbiamo `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Caso 2: dimostriamo `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Supponiamo `~ (forall z : A, P z)`{.hyp} (H).
    - ✅ Ne deduciamo `exists n : A, ~ P n`{.claim} (e).
      - ✅ Per H abbiamo `~ (forall z : A, P z)`{.claim}.
      - ✅ Usando not_all_ex_not otteniamo `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - ✅ Tornando alla definizione di ex (match) in `exists n : A, ~ P n`{.fact} (e), dimostriamo `exists x : A, P x -> forall z : A, P z`{.claim}:
      - ▫️ Consideriamo un elemento arbitrario `t : A`{.var}.
        - ▫️ Supponiamo `~ P t`{.hyp} (i).
          - ▫️ Supponiamo `P t`{.hyp} (h).
            - ✅ Ne deduciamo `False`{.claim} (f).
              - ✅ Per h abbiamo `P t`{.claim}.
              - ✅ Per i abbiamo `~ P t`{.claim}, cioè `P t -> False`{.fact}.
            - ✅ Per contraddizione (False, match), da `False`{.fact} (f) possiamo dedurre `forall z : A, P z`{.claim}.
          - ✅ Abbiamo dimostrato `P t -> forall z : A, P z`{.claim}.
          - ❌ Per definizione di ex (ex_intro) con testimone `t`{.fact}, abbiamo `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.

            <details><summary>not proved: exists x : A, P x -> forall z : A, P z</summary></details>

- ✅ Abbiamo `exists x : A, P x -> forall z : A, P z`{.claim} in tutti i casi.
