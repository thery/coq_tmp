---
require: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# ex_forall

Let `P : nat -> nat -> Prop`{.var}. Assume `exists x : nat, forall y : nat, P x y`{.hyp} (H0). We prove `forall y : nat, exists x : nat, P x y`{.claim}.

- Going back to the definition of ex (match) in `exists x : nat, forall y : nat, P x y`{.fact} (H0), we prove `forall y : nat, exists x : nat, P x y`{.claim}:
  - Let us consider an arbitrary `x : nat`{.var}.
    - Assume `forall y : nat, P x y`{.hyp} (H).
      - Let us consider an arbitrary `y : nat`{.var}.
        - By H we have `forall y0 : nat, P x y0`{.claim}.
        - In particular `P x y`{.claim}.
        - By definition of ex (ex_intro) with witness `x`{.fact}, we have `exists x0 : nat, P x0 y`{.claim} *by eapply @ex_intro; eauto*.
