---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Sia `A : Set`{.var}. Sia `P : A -> Prop`{.var}. Sia `y : A`{.var}. Dimostriamo `exists x : A, P x -> forall z : A, P z`{.claim}.

- Applicando *Classical_Prop.classic*{.just}, abbiamo `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - L'elemento `forall z : A, P z` appartiene a `Prop`.
- Dimostriamo `exists x : A, P x -> forall z : A, P z` per casi su *o*{.just} (*or*{.just}, *match*{.just}):
  - Caso 1: dimostriamo `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Supponiamo `forall z : A, P z`{.hyp} (H).
      - Supponiamo `P y`{.hyp} (_H). Per *H*{.just} abbiamo `forall z : A, P z`{.claim}.
      - Abbiamo dimostrato `P y -> forall z : A, P z`{.claim}.

      Per definizione di ex (*ex_intro*{.just}) con testimone `y`, abbiamo `exists x : A, P x -> forall z : A, P z`{.claim}.
  - Caso 2: dimostriamo `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Supponiamo `~ (forall z : A, P z)`{.hyp} (H).
      - Applicando *Classical_Pred_Type.not_all_ex_not*{.just} a A, P e *H*{.just}, abbiamo `exists n : A, ~ P n`{.claim} (e).
      - Tornando alla definizione di *ex*{.just} (*match*{.just}) in *e*{.just}, dimostriamo `exists x : A, P x -> forall z : A, P z`{.claim}:
        - Scegliamo arbitrariamente `t : A`{.var}; supponiamo `~ P t`{.hyp} (i).
          - Supponiamo `P t`{.hyp} (h).
            - Per applicazione, con *h*{.just}, abbiamo `False`{.claim} (f).
              - Per *i*{.just} abbiamo `~ P t`, cioè `P t -> False`{.claim}.

            Per contraddizione (*False*{.just}, *match*{.just}), da *f*{.just} possiamo dedurre `forall z : A, P z`{.claim}.
          - Abbiamo dimostrato `P t -> forall z : A, P z`{.claim}.

          Per definizione di ex (*ex_intro*{.just}) con testimone `t`, abbiamo `exists x : A, P x -> forall z : A, P z`{.claim}.

      Abbiamo `exists x : A, P x -> forall z : A, P z`{.claim}.

  Abbiamo `exists x : A, P x -> forall z : A, P z`{.claim} in tutti i casi.
