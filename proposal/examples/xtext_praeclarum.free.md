---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (h1) and `x /\ y`{.hyp} (h2). We prove `z /\ t`{.claim}.

[Going back to the definition of and (*and_ind*{.just}) in *h1*{.just}, we prove `z /\ t`{.claim}: [assume `x -> z`{.hyp} (i) and `y -> t`{.hyp} (j); going back to the definition of and (*and_ind*{.just}) in *h2*{.just}, we prove `z /\ t`{.claim}: [assume `x`{.hyp} (k) and `y`{.hyp} (l); [applying *i*{.just} to *k*{.just}, we have `z`{.claim}]{.p}; [applying *j*{.just} to *l*{.just}, we have `t`{.claim}]{.p}; so by definition of and (*conj*{.just}), we have `z /\ t`{.claim}.]{.p}]{.p}]{.p}
