<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas. -->

# and_swap

✅ Let `A B : Prop`. Assume `A /\ B` (H). We prove `B /\ A`.

- ✅ Going back to the definition of and (match) in `A /\ B` (H), we prove `B /\ A`:
  - ▫️ Assume `A` (a) and `B` (b).
    - ✅ By definition of and (conj), from `B` (b) and `A` (a) we deduce `B /\ A` .*by eapply @conj; eauto*

