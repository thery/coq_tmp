---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# ex_forall

✅ Let `P : nat -> nat -> Prop`{.var}. Assume `exists x : nat, forall y : nat, P x y`{.hyp} (H0). We prove `forall y : nat, exists x : nat, P x y`{.claim}.

- ✅ Going back to the definition of ex (match) in *H0*{.just}, we prove `forall y : nat, exists x : nat, P x y`{.claim}:
  - ✅ Let us choose arbitrarily `x : nat`{.var}; assume `forall y : nat, P x y`{.hyp} (H); let us choose arbitrarily `y : nat`{.var}.
    - ✅ Applying *H*{.just} to y, we have `P x y`{.claim}.

    By definition of ex (*ex_intro*{.just}) with witness `x`, we have `exists x0 : nat, P x0 y`{.claim}.
