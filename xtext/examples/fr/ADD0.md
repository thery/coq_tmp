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
  - Considérons un élément arbitraire `m0 : nat`{.var}.
    - Supposons par hypothèse de récurrence `m0 + 0 = m0`{.hyp} (IH).
      - Par IH nous avons `m0 + 0 = m0`{.claim}.
      - En utilisant f_equal nous obtenons `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
      - Nous en déduisons `S (m0 + 0) = S m0`{.claim}.
- Ces cas étant exhaustifs, nous en déduisons `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- En particulier `m + 0 = m`{.claim}.
