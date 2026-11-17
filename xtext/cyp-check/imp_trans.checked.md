<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.lemmas. -->

# imp_trans

✅ Let `A B C : Prop`. Assume `A -> B` (f) and `B -> C` (g) and `A` (a). We prove `C`.

- ✅ We deduce `B`.
  - ✅ By a we have `A`.
  - ✅ By f we have `A -> B`.
- ✅ By g we have `B -> C`.
- ✅ We deduce `C`.

