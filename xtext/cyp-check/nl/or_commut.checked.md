---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

✅ Laat `A B : Prop`{.var}. Stel `A \/ B`{.hyp} (h). We bewijzen `B \/ A`{.claim}.

- ▫️ We bewijzen `B \/ A`{.fact} met gevalsonderscheiding naar `A \/ B`{.fact} (h) (or, or_ind):
- ✅ Geval 1: we bewijzen `A -> B \/ A`{.claim}.
  - ▫️ Stel `A`{.hyp} (i).
    - ✅ Volgens de definitie van or (or_intror), uit `A`{.fact} (i) hieruit volgt `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- ✅ Geval 2: we bewijzen `B -> B \/ A`{.claim}.
  - ▫️ Stel `B`{.hyp} (j).
    - ✅ Volgens de definitie van or (or_introl), uit `B`{.fact} (j) hieruit volgt `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- ✅ Er geldt `B \/ A`{.claim} in alle gevallen.
