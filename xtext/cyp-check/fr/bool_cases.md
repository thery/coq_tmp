---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: fr
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Soit `b : bool`{.var}. Montrons `b = true \/ b = false`{.claim}.

- Montrons `b = true \/ b = false` par analyse de cas sur *b*{.just} (*bool*{.just}, *match*{.just}):
  - Cas 1: montrons `true = true \/ true = false`{.claim}.
    - Par définition de eq (*eq_refl*{.just}), nous avons `true = true`{.claim}.
    - Par définition de or (*or_introl*{.just}), nous avons `true = true \/ true = false`{.claim}.
  - Cas 2: montrons `false = true \/ false = false`{.claim}.
    - Par définition de eq (*eq_refl*{.just}), nous avons `false = false`{.claim}.
    - Par définition de or (*or_intror*{.just}), nous avons `false = true \/ false = false`{.claim}.

  Ces cas étant exhaustifs, nous en déduisons `b = true \/ b = false`{.claim}.
