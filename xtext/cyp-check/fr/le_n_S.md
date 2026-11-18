---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: fr
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

Soient `n m : nat`{.var}. Supposons `n <= m`{.hyp} (H). Montrons `S n <= S m`{.claim}.

- Montrons `S n <= S m`{.fact} par récurrence sur `n <= m`{.fact} (H) (le, le_ind):
- Cas 1 (base): montrons `S n <= S n`{.claim}.
  - Par définition de le (le_n), nous avons `S n <= S n`{.claim} *by Corelib.Init.Peano.le_n*.
- Cas 2 (inductif): montrons `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - Considérons un élément arbitraire `m0 : nat`{.var}.
    - Supposons `n <= m0`{.hyp} (H0) et par hypothèse de récurrence `S n <= S m0`{.hyp} (IH).
      - Par définition de le (le_S) avec le témoin `S m0`{.fact}, à partir de `S n <= S m0`{.fact} (IH) nous en déduisons `S n <= S (S m0)`{.claim} *by Corelib.Init.Peano.le_S*.
- Nous avons `S n <= S m`{.claim} dans tous les cas.
