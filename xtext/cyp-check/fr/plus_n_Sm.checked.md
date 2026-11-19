---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: fr
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

✅ Soient `n m : nat`{.var}. Montrons `S (n + m) = n + S m`{.claim}.

- ✅ Montrons `S (n + m) = n + S m` par récurrence sur `n` (nat, *nat_ind*{.just}):
  - ✅ Cas 1 (base): montrons `0 + S m = 0 + S m`{.claim}.
    - ✅ Par définition de eq (*eq_refl*{.just}), nous avons `0 + S m = 0 + S m`{.claim}.
  - ✅ Cas 2 (inductif): montrons `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
    - ✅ Choisissons arbitrairement `n0 : nat`{.var}; supposons par hypothèse de récurrence `S (n0 + m) = n0 + S m`{.hyp} (IH).
      - ✅ Par définition de eq (*eq_refl*{.just}), nous avons `S (n0 + S m) = S (n0 + S m)`{.claim}.
      - ✅ Par *IH*{.just} nous avons `S (n0 + m) = n0 + S m`{.claim}.

      En réécrivant avec `S (n0 + m) = n0 + S m`{.fact} de droite à gauche (eq_ind_r), nous obtenons `S (S (n0 + m)) = S (n0 + S m)`{.claim}.

  Ces cas étant exhaustifs, nous en déduisons `S (n + m) = n + S m`{.claim}.
