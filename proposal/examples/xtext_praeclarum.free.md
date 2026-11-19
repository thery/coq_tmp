---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (h1) and `x /\ y`{.hyp} (h2). We prove `z /\ t`{.claim}.

[Going back to the definition of and (*and_ind*) in *h1*, we prove `z /\ t`{.claim}: [assume `x -> z`{.hyp} (i) and `y -> t`{.hyp} (j); going back to the definition of and (*and_ind*) in *h2*, we prove `z /\ t`{.claim}: [assume `x`{.hyp} (k) and `y`{.hyp} (l); [applying *i* to *k*, we have `z`{.claim}]{.p}; [applying *j* to *l*, we have `t`{.claim}]{.p}; so by definition of and (*conj*), we have `z /\ t`{.claim}.]{.p}]{.p}]{.p}
