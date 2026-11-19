---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Soient `A B : Prop`{.var}. Supposons `A \/ B`{.hyp} (h). Montrons `B \/ A`{.claim}.

- Montrons `B \/ A` par analyse de cas sur *h*{.just} (or, *or_ind*{.just}):
  - Cas 1: montrons `A -> B \/ A`{.claim}.
    - Supposons `A`{.hyp} (i). Par définition de or (*or_intror*{.just}), à partir de *i*{.just} nous en déduisons `B \/ A`{.claim}.
  - Cas 2: montrons `B -> B \/ A`{.claim}.
    - Supposons `B`{.hyp} (j). Par définition de or (*or_introl*{.just}), à partir de *j*{.just} nous en déduisons `B \/ A`{.claim}.

  Nous avons `B \/ A`{.claim} dans tous les cas.
