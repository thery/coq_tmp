---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: nl
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

✅ Laat `A B : Prop`{.var}. Stel `A \/ B`{.hyp} (h). We bewijzen `B \/ A`{.claim}.

- ✅ We bewijzen `B \/ A` met gevalsonderscheiding naar *h*{.just} (*or*{.just}, *match*{.just}):
  - ✅ Geval 1: we bewijzen `A -> B \/ A`{.claim}.
    - ✅ Stel `A`{.hyp} (i). Volgens de definitie van or (*or_intror*{.just}), uit *i*{.just} hieruit volgt `B \/ A`{.claim}.
  - ✅ Geval 2: we bewijzen `B -> B \/ A`{.claim}.
    - ✅ Stel `B`{.hyp} (j). Volgens de definitie van or (*or_introl*{.just}), uit *j*{.just} hieruit volgt `B \/ A`{.claim}.

  Er geldt `B \/ A`{.claim} in alle gevallen.
