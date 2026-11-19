---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

✅ Seien `A B : Prop`{.var}. Angenommen `A \/ B`{.hyp} (h). Wir zeigen `B \/ A`{.claim}.

- ✅ Wir zeigen `B \/ A` durch Fallunterscheidung über *h*{.just} (or, *or_ind*{.just}):
  - ✅ Fall 1: wir zeigen `A -> B \/ A`{.claim}.
    - ✅ Angenommen `A`{.hyp} (i). Nach Definition von or (*or_intror*{.just}), aus *i*{.just} daraus folgt `B \/ A`{.claim}.
  - ✅ Fall 2: wir zeigen `B -> B \/ A`{.claim}.
    - ✅ Angenommen `B`{.hyp} (j). Nach Definition von or (*or_introl*{.just}), aus *j*{.just} daraus folgt `B \/ A`{.claim}.

  Es gilt `B \/ A`{.claim} in allen Fällen.
