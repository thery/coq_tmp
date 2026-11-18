---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: fr
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Soit `b : bool`{.var}. Montrons `b = true \/ b = false`{.claim}.

- Montrons `b = true \/ b = false`{.fact} par analyse de cas sur `b`{.fact} (bool, match):
- Cas 1: montrons `true = true \/ true = false`{.claim}.
  - Par définition de eq (eq_refl), nous avons `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Par définition de or (or_introl), nous avons `true = true \/ true = false`{.claim} *by Corelib.Init.Logic.or_introl*.
- Cas 2: montrons `false = true \/ false = false`{.claim}.
  - Par définition de eq (eq_refl), nous avons `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Par définition de or (or_intror), nous avons `false = true \/ false = false`{.claim} *by Corelib.Init.Logic.or_intror*.
- Ces cas étant exhaustifs, nous en déduisons `b = true \/ b = false`{.claim}.
