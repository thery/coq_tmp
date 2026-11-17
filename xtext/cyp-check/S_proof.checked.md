<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper. -->

# S_proof

✅ Let `A B C : Prop`. Assume `A -> B -> C` (h) and `A -> B` (h0) and `A` (h1). We prove `C`.

- ✅ By h1 we have `A`.
- ✅ We deduce `B`.
  - ✅ By h1 we have `A`.
  - ✅ By h0 we have `A -> B`.
- ✅ By h we have `A -> B -> C`.
- ✅ We deduce `C`.

