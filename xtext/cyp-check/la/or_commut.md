---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Sint `A B : Prop`{.var}. Ponamus `A \/ B`{.hyp} (h). Ostendamus `B \/ A`{.claim}.

- Ostendamus `B \/ A` per casus in *h*{.just} (or, *or_ind*{.just}):
  - Casus 1: ostendamus `A -> B \/ A`{.claim}.
    - Ponamus `A`{.hyp} (i). Ex definitione or (*or_intror*{.just}), ex *i*{.just} unde sequitur `B \/ A`{.claim}.
  - Casus 2: ostendamus `B -> B \/ A`{.claim}.
    - Ponamus `B`{.hyp} (j). Ex definitione or (*or_introl*{.just}), ex *j*{.just} unde sequitur `B \/ A`{.claim}.

  Habemus `B \/ A`{.claim} in omnibus casibus.
