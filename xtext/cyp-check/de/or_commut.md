---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Seien `A B : Prop`{.var}. Angenommen `A \/ B`{.hyp} (h). Wir zeigen `B \/ A`{.claim}.

- Wir zeigen `B \/ A`{.fact} durch Fallunterscheidung über `A \/ B`{.fact} (h) (or, or_ind):
- Fall 1: wir zeigen `A -> B \/ A`{.claim}.
  - Angenommen `A`{.hyp} (i).
    - Nach Definition von or (or_intror), aus `A`{.fact} (i) daraus folgt `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- Fall 2: wir zeigen `B -> B \/ A`{.claim}.
  - Angenommen `B`{.hyp} (j).
    - Nach Definition von or (or_introl), aus `B`{.fact} (j) daraus folgt `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- Es gilt `B \/ A`{.claim} in allen Fällen.
