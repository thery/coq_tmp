---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Siano `A B : Prop`{.var}. Supponiamo `A \/ B`{.hyp} (h). Dimostriamo `B \/ A`{.claim}.

- Dimostriamo `B \/ A` per casi su *h*{.just} (*or*{.just}, *match*{.just}):
  - Caso 1: dimostriamo `A -> B \/ A`{.claim}.
    - Supponiamo `A`{.hyp} (i). Per definizione di or (*or_intror*{.just}), da *i*{.just} ne deduciamo `B \/ A`{.claim}.
  - Caso 2: dimostriamo `B -> B \/ A`{.claim}.
    - Supponiamo `B`{.hyp} (j). Per definizione di or (*or_introl*{.just}), da *j*{.just} ne deduciamo `B \/ A`{.claim}.

  Abbiamo `B \/ A`{.claim} in tutti i casi.
