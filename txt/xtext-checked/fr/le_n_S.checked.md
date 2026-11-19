---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ Soient `n m : nat`{.var}. Supposons `n <= m`{.hyp} (H). Montrons `S n <= S m`{.claim}.

- ✅ Montrons `S n <= S m` par récurrence sur *H*{.just} (le, le_ind):
  - ✅ Cas 1 (base): montrons `S n <= S n`{.claim}.
    - ✅ Par définition de le (*le_n*{.just}), nous avons `S n <= S n`{.claim}.
  - ✅ Cas 2 (inductif): montrons `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
    - ✅ Choisissons arbitrairement `m0 : nat`{.var}; supposons `n <= m0`{.hyp} (H0) et par hypothèse de récurrence `S n <= S m0`{.hyp} (IH). Par définition de le (*le_S*{.just}) avec le témoin `S m0`, à partir de *IH*{.just} nous en déduisons `S n <= S (S m0)`{.claim}.

  Nous avons `S n <= S m`{.claim} dans tous les cas.
