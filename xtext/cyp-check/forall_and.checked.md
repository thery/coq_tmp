<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas. -->

# forall_and

✅ Let `P Q : nat -> Prop`. Assume `forall x : nat, P x /\ Q x` (H). Let `x : nat`. We prove `P x`.

- ✅ In particular `P x /\ Q x` (a).
  - ✅ By H we have `forall x0 : nat, P x0 /\ Q x0`.
- ✅ Going back to the definition of and (match) in `P x /\ Q x` (a), we prove `P x`:
  - ▫️ Assume `P x` (p) and `Q x` (_H).
    - ✅ By p we have `P x`.

