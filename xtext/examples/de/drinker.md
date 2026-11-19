---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Sei `A : Set`{.var}. Sei `P : A -> Prop`{.var}. Sei `y : A`{.var}. Wir zeigen `exists x : A, P x -> forall z : A, P z`{.claim}.

- Durch Anwendung von *Classical_Prop.classic*{.just}, es gilt `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Das Element `forall z : A, P z` gehört zu `Prop`.
- Wir zeigen `exists x : A, P x -> forall z : A, P z` durch Fallunterscheidung über *o*{.just} (or, match):
  - Fall 1: wir zeigen `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Angenommen `forall z : A, P z`{.hyp} (H).
      - Angenommen `P y`{.hyp} (_H). Nach *H*{.just} es gilt `forall z : A, P z`{.claim}.
      - Wir haben gezeigt `P y -> forall z : A, P z`{.claim}.

      Nach Definition von ex (*ex_intro*{.just}) mit dem Zeugen `y`, es gilt `exists x : A, P x -> forall z : A, P z`{.claim}.
  - Fall 2: wir zeigen `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Angenommen `~ (forall z : A, P z)`{.hyp} (H).
      - Durch Anwendung von *Classical_Pred_Type.not_all_ex_not*{.just} auf A, P und *H*{.just}, es gilt `exists n : A, ~ P n`{.claim} (e).
      - Zurück zur Definition von ex (match) in *e*{.just}, wir zeigen `exists x : A, P x -> forall z : A, P z`{.claim}:
        - Seien beliebig `t : A`{.var}; angenommen `~ P t`{.hyp} (i).
          - Angenommen `P t`{.hyp} (h).
            - Durch Anwendung, mit *h*{.just}, es gilt `False`{.claim} (f).
              - Nach *i*{.just} es gilt `~ P t`, das heißt `P t -> False`{.claim}.

            Durch Widerspruch (False, match), aus *f*{.just} können wir folgern `forall z : A, P z`{.claim}.
          - Wir haben gezeigt `P t -> forall z : A, P z`{.claim}.

          Nach Definition von ex (*ex_intro*{.just}) mit dem Zeugen `t`, es gilt `exists x : A, P x -> forall z : A, P z`{.claim}.

      Es gilt `exists x : A, P x -> forall z : A, P z`{.claim}.

  Es gilt `exists x : A, P x -> forall z : A, P z`{.claim} in allen Fällen.
