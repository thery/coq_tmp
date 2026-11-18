---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Sint `A B : Prop`{.var}. Ponamus `A \/ B`{.hyp} (h). Ostendamus `B \/ A`{.claim}.

- Ostendamus `B \/ A`{.fact} per casus in `A \/ B`{.fact} (h) (or, or_ind):
- Casus 1: ostendamus `A -> B \/ A`{.claim}.
  - Ponamus `A`{.hyp} (i).
    - Ex definitione or (or_intror), ex `A`{.fact} (i) unde sequitur `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- Casus 2: ostendamus `B -> B \/ A`{.claim}.
  - Ponamus `B`{.hyp} (j).
    - Ex definitione or (or_introl), ex `B`{.fact} (j) unde sequitur `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- Habemus `B \/ A`{.claim} in omnibus casibus.
