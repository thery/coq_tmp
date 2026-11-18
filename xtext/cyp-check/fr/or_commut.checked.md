---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

✅ Soient `A B : Prop`{.var}. Supposons `A \/ B`{.hyp} (h). Montrons `B \/ A`{.claim}.

- ▫️ Montrons `B \/ A`{.fact} par analyse de cas sur `A \/ B`{.fact} (h) (or, or_ind):
- ✅ Cas 1: montrons `A -> B \/ A`{.claim}.
  - ▫️ Supposons `A`{.hyp} (i).
    - ✅ Par définition de or (or_intror), à partir de `A`{.fact} (i) nous en déduisons `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- ✅ Cas 2: montrons `B -> B \/ A`{.claim}.
  - ▫️ Supposons `B`{.hyp} (j).
    - ✅ Par définition de or (or_introl), à partir de `B`{.fact} (j) nous en déduisons `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- ✅ Nous avons `B \/ A`{.claim} dans tous les cas.
