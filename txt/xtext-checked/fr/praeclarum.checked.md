---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

✅ Soient `x y z t : Prop`{.var}. Supposons `(x -> z) /\ (y -> t)`{.hyp} (h1) et `x /\ y`{.hyp} (h2). Montrons `z /\ t`{.claim}.

- ✅ En revenant à la définition de *and*{.just} (*match*{.just}) dans *h1*{.just}, montrons `z /\ t`{.claim}:
  - ✅ Supposons `x -> z`{.hyp} (i) et `y -> t`{.hyp} (j). En revenant à la définition de *and*{.just} (*match*{.just}) dans *h2*{.just}, montrons `z /\ t`{.claim}:
    - ✅ Supposons `x`{.hyp} (k) et `y`{.hyp} (l).
      - ✅ En appliquant *i*{.just} à *k*{.just}, nous avons `z`{.claim}.
      - ✅ En appliquant *j*{.just} à *l*{.just}, nous avons `t`{.claim}.

      Donc par définition de and (*conj*{.just}), nous avons `z /\ t`{.claim}.
