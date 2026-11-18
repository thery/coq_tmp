---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Пусть `A B : Prop`{.var}. Предположим, что `A \/ B`{.hyp} (h). Докажем, что `B \/ A`{.claim}.

- Докажем, что `B \/ A`{.fact} разбором случаев по `A \/ B`{.fact} (h) (or, or_ind):
- Случай 1: докажем, что `A -> B \/ A`{.claim}.
  - Предположим, что `A`{.hyp} (i).
    - По определению or (or_intror), из `A`{.fact} (i) следовательно `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- Случай 2: докажем, что `B -> B \/ A`{.claim}.
  - Предположим, что `B`{.hyp} (j).
    - По определению or (or_introl), из `B`{.fact} (j) следовательно `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- Имеем `B \/ A`{.claim} во всех случаях.
