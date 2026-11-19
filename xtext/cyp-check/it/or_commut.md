---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Siano `A B : Prop`{.var}. Supponiamo `A \/ B`{.hyp} (h). Dimostriamo `B \/ A`{.claim}.

- Dimostriamo `B \/ A`{.fact} per casi su `A \/ B`{.fact} (h) (or, or_ind):
- Caso 1: dimostriamo `A -> B \/ A`{.claim}.
  - Supponiamo `A`{.hyp} (i).
    - Per definizione di or (or_intror), da `A`{.fact} (i) ne deduciamo `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- Caso 2: dimostriamo `B -> B \/ A`{.claim}.
  - Supponiamo `B`{.hyp} (j).
    - Per definizione di or (or_introl), da `B`{.fact} (j) ne deduciamo `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- Abbiamo `B \/ A`{.claim} in tutti i casi.
