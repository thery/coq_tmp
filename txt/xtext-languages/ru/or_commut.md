---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Пусть `A B : Prop`{.var}. Предположим, что `A \/ B`{.hyp} (h). Докажем, что `B \/ A`{.claim}.

- Докажем, что `B \/ A` разбором случаев по *h*{.just} (*or*{.just}, *match*{.just}):
  - Случай 1: докажем, что `A -> B \/ A`{.claim}.
    - Предположим, что `A`{.hyp} (i). По определению or (*or_intror*{.just}), из *i*{.just} следовательно `B \/ A`{.claim}.
  - Случай 2: докажем, что `B -> B \/ A`{.claim}.
    - Предположим, что `B`{.hyp} (j). По определению or (*or_introl*{.just}), из *j*{.just} следовательно `B \/ A`{.claim}.

  Имеем `B \/ A`{.claim} во всех случаях.
