---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# ex_forall

Let `P : nat -> nat -> Prop`{.var}. Assume `exists x : nat, forall y : nat, P x y`{.hyp} (H0). We prove `forall y : nat, exists x : nat, P x y`{.claim}.

- Going back to the definition of ex (match) in `exists x : nat, forall y : nat, P x y`{.fact} (H0), we prove `forall y : nat, exists x : nat, P x y`{.claim}:
  - Let us choose arbitrarily `x : nat`{.var}.
    - Assume `forall y : nat, P x y`{.hyp} (H).
      - Let us choose arbitrarily `y : nat`{.var}.
        - By H we have `forall elpi_ctx_entry_5_ : nat, P x elpi_ctx_entry_5_`{.claim}.
        - The element `y`{.fact} belongs to `nat`{.fact}.
        - By application, we have `P x y`{.claim}.
        - By definition of ex (ex_intro) with witness `x`{.fact}, we have `exists x0 : nat, P x0 y`{.claim} *by Corelib.Init.Logic.ex_intro*.
