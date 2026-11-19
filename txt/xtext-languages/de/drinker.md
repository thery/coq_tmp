---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Sei `A : Set`{.var}. Sei `P : A -> Prop`{.var}. Sei `y : A`{.var}. Wir zeigen `exists x : A, P x -> forall z : A, P z`{.claim}.

- Durch Anwendung von classic, es gilt `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Das Element `forall z : A, P z`{.fact} gehört zu `Prop`{.fact}.
- Wir zeigen `exists x : A, P x -> forall z : A, P z`{.fact} durch Fallunterscheidung über `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- Fall 1: wir zeigen `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Angenommen `forall z : A, P z`{.hyp} (H).
    - Angenommen `P y`{.hyp} (_H).
      - Nach H es gilt `forall z : A, P z`{.claim}.
    - Wir haben gezeigt `P y -> forall z : A, P z`{.claim}.
    - Nach Definition von ex (ex_intro) mit dem Zeugen `y`{.fact}, es gilt `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Fall 2: wir zeigen `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Angenommen `~ (forall z : A, P z)`{.hyp} (H).
    - Durch Anwendung von not_all_ex_not auf A, P und H, es gilt `exists n : A, ~ P n`{.claim} (e).
    - Zurück zur Definition von ex (match) in `exists n : A, ~ P n`{.fact} (e), wir zeigen `exists x : A, P x -> forall z : A, P z`{.claim}:
      - Seien beliebig `t : A`{.var}; angenommen `~ P t`{.hyp} (i).
        - Angenommen `P t`{.hyp} (h).
          - Durch Anwendung, mit h, es gilt `False`{.claim} (f).
            - Nach i es gilt `~ P t`{.claim}, das heißt `P t -> False`{.fact}.
          - Durch Widerspruch (False, match), aus `False`{.fact} (f) können wir folgern `forall z : A, P z`{.claim}.
        - Wir haben gezeigt `P t -> forall z : A, P z`{.claim}.
        - Nach Definition von ex (ex_intro) mit dem Zeugen `t`{.fact}, es gilt `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Es gilt `exists x : A, P x -> forall z : A, P z`{.claim} in allen Fällen.
