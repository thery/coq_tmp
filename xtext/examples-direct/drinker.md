---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Let `A : Set`{.var}. Let `P : A -> Prop`{.var}. Let `y : A`{.var}. We prove `exists x : A, P x -> forall z : A, P z`{.claim}.

- In particular `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Using classic we get `forall P0 : Prop, P0 \/ ~ P0`{.claim} *by Stdlib.Logic.Classical_Prop.classic*.
- We prove `exists x : A, P x -> forall z : A, P z`{.fact} by case analysis on `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- Case 1: we prove `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Assume `forall z : A, P z`{.hyp} (H).
    - Assume `P y`{.hyp} (_H).
      - By H we have `forall z : A, P z`{.claim}.
    - We have proved `P y -> forall z : A, P z`{.claim}.
    - By definition of ex (ex_intro) with witness `y`{.fact}, we have `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Case 2: we prove `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Assume `~ (forall z : A, P z)`{.hyp} (H).
    - We deduce `exists n : A, ~ P n`{.claim} (e).
      - By H we have `~ (forall z : A, P z)`{.claim}.
      - Using not_all_ex_not we get `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - Going back to the definition of ex (match) in `exists n : A, ~ P n`{.fact} (e), we prove `exists x : A, P x -> forall z : A, P z`{.claim}:
      - Let us consider an arbitrary `t : A`{.var}.
        - Assume `~ P t`{.hyp} (i).
          - Assume `P t`{.hyp} (h).
            - We deduce `False`{.claim} (f).
              - By h we have `P t`{.claim}.
              - By i we have `~ P t`{.claim}, that is `P t -> False`{.fact}.
            - By contradiction (False, match), from `False`{.fact} (f) we can deduce `forall z : A, P z`{.claim}.
          - We have proved `P t -> forall z : A, P z`{.claim}.
          - By definition of ex (ex_intro) with witness `t`{.fact}, we have `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- We have `exists x : A, P x -> forall z : A, P z`{.claim} in all cases.
