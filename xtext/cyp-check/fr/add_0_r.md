---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: fr
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Soit `n : nat`{.var}. Montrons `n + 0 = n`{.claim}.

- Montrons `n + 0 = n` par récurrence sur *n*{.just} (*nat*{.just}, *induction*{.just}):
  - Cas 1 (base): montrons `0 = 0`{.claim}.
    - Par définition de eq (*eq_refl*{.just}), nous avons `0 = 0`{.claim}.
  - Cas 2 (inductif): montrons `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
    - Choisissons arbitrairement `m : nat`{.var}; supposons par hypothèse de récurrence `m + 0 = m`{.hyp} (IH).
      - Par définition de eq (*eq_refl*{.just}), nous avons `S m = S m`{.claim}.
      - Par *IH*{.just} nous avons `m + 0 = m`{.claim}.

      En réécrivant avec `m + 0 = m`{.fact} de droite à gauche (eq_ind_r), nous obtenons `S (m + 0) = S m`{.claim}.

  Ces cas étant exhaustifs, nous en déduisons `n + 0 = n`{.claim}.
