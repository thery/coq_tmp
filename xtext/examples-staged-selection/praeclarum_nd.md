---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_nd

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H1) and `x /\ y`{.hyp} (H2). We prove `z /\ t`{.claim}.

- Applying *proj1*{.just} to *H1*{.just}, we have `z`{.claim}.
  - The element `x -> z` belongs to `Prop`.
  - The element `y -> t` belongs to `Prop`.
  - Applying *proj1*{.just} to x, y and *H2*{.just}, we have `x`{.claim}.
- Applying *proj2*{.just} to *H1*{.just}, we have `t`{.claim}.
  - The element `x -> z` belongs to `Prop`.
  - The element `y -> t` belongs to `Prop`.
  - Applying *proj2*{.just} to x, y and *H2*{.just}, we have `y`{.claim}.
- So by definition of and (*conj*{.just}), we have `z /\ t`{.claim}.
