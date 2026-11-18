---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: fr
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Soit `n : nat`{.var}. Montrons `n + 0 = n`{.claim}.

- Pour montrer `n + 0 = n`{.fact} par récurrence (nat, nat_ind), nous le généralisons en `forall n0 : nat, n0 + 0 = n0`{.fact}:
- Cas 1 (base): montrons `0 = 0`{.claim}.
  - Par définition de eq (eq_refl), nous avons `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Cas 2 (inductif): montrons `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - Choisissons arbitrairement `m : nat`{.var}; supposons par hypothèse de récurrence `m + 0 = m`{.hyp} (IH).
    - Par définition de eq (eq_refl), nous avons `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Par IH nous avons `m + 0 = m`{.claim}.
    - En réécrivant avec `m + 0 = m`{.fact} de droite à gauche (eq_ind_r), nous obtenons `S (m + 0) = S m`{.claim}.
- Ces cas étant exhaustifs, nous en déduisons `forall n0 : nat, n0 + 0 = n0`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- En particulier `n + 0 = n`{.claim}.
