---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Let `A : Set`{.var}. Let `P : A -> Prop`{.var}. Let `y : A`{.var}. We prove `exists x : A, P x -> forall z : A, P z`{.claim}.

- Applying classic, we have `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - The element `forall z : A, P z`{.fact} belongs to `Prop`{.fact}.
- We prove `exists x : A, P x -> forall z : A, P z`{.fact} by case analysis on `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- Case 1: we prove `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Assume `forall z : A, P z`{.hyp} (H).
    - Assume `P y`{.hyp} (_H).
      - By H we have `forall z : A, P z`{.claim}.
    - We have proved `P y -> forall z : A, P z`{.claim}.
    - By definition of ex (ex_intro) with witness `y`{.fact}, we have `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Case 2: we prove `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Assume `~ (forall z : A, P z)`{.hyp} (H).
    - Applying not_all_ex_not to A, P and H, we have `exists n : A, ~ P n`{.claim} (e).
    - Going back to the definition of ex (match) in `exists n : A, ~ P n`{.fact} (e), we prove `exists x : A, P x -> forall z : A, P z`{.claim}:
      - Let us choose arbitrarily `t : A`{.var}; assume `~ P t`{.hyp} (i).
        - Assume `P t`{.hyp} (h).
          - By application, with h, we have `False`{.claim} (f).
            - By i we have `~ P t`{.claim}, that is `P t -> False`{.fact}.
          - By contradiction (False, match), from `False`{.fact} (f) we can deduce `forall z : A, P z`{.claim}.
        - We have proved `P t -> forall z : A, P z`{.claim}.
        - By definition of ex (ex_intro) with witness `t`{.fact}, we have `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- We have `exists x : A, P x -> forall z : A, P z`{.claim} in all cases.
