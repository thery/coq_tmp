---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Let `A : Set`{.var}. Let `P : A -> Prop`{.var}. Let `y : A`{.var}. We prove `exists x : A, P x -> forall z : A, P z`{.claim}.

- Applying *Classical_Prop.classic*{.just}, we have `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - The element `forall z : A, P z` belongs to `Prop`.
- We prove `exists x : A, P x -> forall z : A, P z` by case analysis on *o*{.just} (*or*{.just}, *match*{.just}):
  - Case 1: we prove `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Assume `forall z : A, P z`{.hyp} (H).
      - Assume `P y`{.hyp} (_H). By *H*{.just} we have `forall z : A, P z`{.claim}.
      - We have proved `P y -> forall z : A, P z`{.claim}.

      By definition of ex (*ex_intro*{.just}) with witness `y`, we have `exists x : A, P x -> forall z : A, P z`{.claim}.
  - Case 2: we prove `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Assume `~ (forall z : A, P z)`{.hyp} (H).
      - Applying *Classical_Pred_Type.not_all_ex_not*{.just} to A, P and *H*{.just}, we have `exists n : A, ~ P n`{.claim} (e).
      - Going back to the definition of *ex*{.just} (*match*{.just}) in *e*{.just}, we prove `exists x : A, P x -> forall z : A, P z`{.claim}:
        - Let us choose arbitrarily `t : A`{.var}; assume `~ P t`{.hyp} (i).
          - Assume `P t`{.hyp} (h).
            - By application, with *h*{.just}, we have `False`{.claim} (f).
              - By *i*{.just} we have `~ P t`, that is `P t -> False`{.claim}.

            By contradiction (*False*{.just}, *match*{.just}), from *f*{.just} we can deduce `forall z : A, P z`{.claim}.
          - We have proved `P t -> forall z : A, P z`{.claim}.

          By definition of ex (*ex_intro*{.just}) with witness `t`, we have `exists x : A, P x -> forall z : A, P z`{.claim}.

      We have `exists x : A, P x -> forall z : A, P z`{.claim}.

  We have `exists x : A, P x -> forall z : A, P z`{.claim} in all cases.
