---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ Sia `A : Set`{.var}. Sia `P : A -> Prop`{.var}. Sia `y : A`{.var}. Dimostriamo `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ Applicando classic, abbiamo `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ L'elemento `forall z : A, P z`{.fact} appartiene a `Prop`{.fact}.
- ▫️ Dimostriamo `exists x : A, P x -> forall z : A, P z`{.fact} per casi su `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- ✅ Caso 1: dimostriamo `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Supponiamo `forall z : A, P z`{.hyp} (H).
    - ▫️ Supponiamo `P y`{.hyp} (_H).
      - ✅ Per H abbiamo `forall z : A, P z`{.claim}.
    - ✅ Abbiamo dimostrato `P y -> forall z : A, P z`{.claim}.
    - ✅ Per definizione di ex (ex_intro) con testimone `y`{.fact}, abbiamo `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Caso 2: dimostriamo `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Supponiamo `~ (forall z : A, P z)`{.hyp} (H).
    - ❌ Applicando not_all_ex_not a A, P e H, abbiamo `exists n : A, ~ P n`{.claim} (e).

      <details><summary>non dimostrato: exists n : A, ~ P n</summary></details>

    - ✅ Tornando alla definizione di ex (match) in `exists n : A, ~ P n`{.fact} (e), dimostriamo `exists x : A, P x -> forall z : A, P z`{.claim}:
      - ▫️ Scegliamo arbitrariamente `t : A`{.var}; supponiamo `~ P t`{.hyp} (i).
        - ▫️ Supponiamo `P t`{.hyp} (h).
          - ✅ Per applicazione, con h, abbiamo `False`{.claim} (f).
            - ✅ Per i abbiamo `~ P t`{.claim}, cioè `P t -> False`{.fact}.
          - ✅ Per contraddizione (False, match), da `False`{.fact} (f) possiamo dedurre `forall z : A, P z`{.claim}.
        - ✅ Abbiamo dimostrato `P t -> forall z : A, P z`{.claim}.
        - ✅ Per definizione di ex (ex_intro) con testimone `t`{.fact}, abbiamo `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Abbiamo `exists x : A, P x -> forall z : A, P z`{.claim} in tutti i casi.
