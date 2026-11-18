---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ Sei `A : Set`{.var}. Sei `P : A -> Prop`{.var}. Sei `y : A`{.var}. Wir zeigen `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ Insbesondere `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ✅ Mit classic wir erhalten `forall P0 : Prop, P0 \/ ~ P0`{.claim} *by Stdlib.Logic.Classical_Prop.classic*.
- ▫️ Wir zeigen `exists x : A, P x -> forall z : A, P z`{.fact} durch Fallunterscheidung über `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- ✅ Fall 1: wir zeigen `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Angenommen `forall z : A, P z`{.hyp} (H).
    - ▫️ Angenommen `P y`{.hyp} (_H).
      - ✅ Nach H es gilt `forall z : A, P z`{.claim}.
    - ✅ Wir haben gezeigt `P y -> forall z : A, P z`{.claim}.
    - ✅ Nach Definition von ex (ex_intro) mit dem Zeugen `y`{.fact}, es gilt `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Fall 2: wir zeigen `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ Angenommen `~ (forall z : A, P z)`{.hyp} (H).
    - ✅ Daraus folgt `exists n : A, ~ P n`{.claim} (e).
      - ✅ Nach H es gilt `~ (forall z : A, P z)`{.claim}.
      - ✅ Mit not_all_ex_not wir erhalten `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - ✅ Zurück zur Definition von ex (match) in `exists n : A, ~ P n`{.fact} (e), wir zeigen `exists x : A, P x -> forall z : A, P z`{.claim}:
      - ▫️ Sei beliebig `t : A`{.var}.
        - ▫️ Angenommen `~ P t`{.hyp} (i).
          - ▫️ Angenommen `P t`{.hyp} (h).
            - ✅ Daraus folgt `False`{.claim} (f).
              - ✅ Nach h es gilt `P t`{.claim}.
              - ✅ Nach i es gilt `~ P t`{.claim}, das heißt `P t -> False`{.fact}.
            - ✅ Durch Widerspruch (False, match), aus `False`{.fact} (f) können wir folgern `forall z : A, P z`{.claim}.
          - ✅ Wir haben gezeigt `P t -> forall z : A, P z`{.claim}.
          - ❌ Nach Definition von ex (ex_intro) mit dem Zeugen `t`{.fact}, es gilt `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.

            <details><summary>not proved: exists x : A, P x -> forall z : A, P z</summary></details>

- ✅ Es gilt `exists x : A, P x -> forall z : A, P z`{.claim} in allen Fällen.
