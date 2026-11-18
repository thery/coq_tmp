---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Soit `m : nat`{.var}. Montrons `m + 0 = m`{.claim}.

- Pour montrer `m + 0 = m`{.fact} par récurrence (nat, nat_ind), nous le généralisons en `forall n : nat, n + 0 = n`{.fact}:
- Cas 1 (base): montrons `0 + 0 = 0 + 0`{.claim}.
  - Par définition de eq (eq_refl), nous avons `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Cas 2 (inductif): montrons `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Choisissons arbitrairement `m0 : nat`{.var}; supposons par hypothèse de récurrence `m0 + 0 = m0`{.hyp} (IH).
    - L'élément `nat`{.fact} appartient à `Type`{.fact}.
    - L'élément `nat`{.fact} appartient à `Type`{.fact}.
    - L'élément `S`{.fact} appartient à `nat -> nat`{.fact}.
    - L'élément `m0 + 0`{.fact} appartient à `nat`{.fact}.
    - L'élément `m0`{.fact} appartient à `nat`{.fact}.
    - Par IH nous avons `m0 + 0 = m0`{.claim}.
    - En appliquant f_equal, nous avons `S (m0 + 0) = S m0`{.claim}.
- Ces cas étant exhaustifs, nous en déduisons `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- En particulier `m + 0 = m`{.claim}.
