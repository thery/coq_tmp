---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Seien `x y z t : Prop`{.var}. Angenommen `(x -> z) /\ (y -> t)`{.hyp} (h1) und `x /\ y`{.hyp} (h2). Wir zeigen `z /\ t`{.claim}.

- Zurück zur Definition von and (and_ind) in `(x -> z) /\ (y -> t)`{.fact} (h1), wir zeigen `z /\ t`{.claim}:
  - Angenommen `x -> z`{.hyp} (i) und `y -> t`{.hyp} (j).
    - Zurück zur Definition von and (and_ind) in `x /\ y`{.fact} (h2), wir zeigen `z /\ t`{.claim}:
      - Angenommen `x`{.hyp} (k) und `y`{.hyp} (l).
        - Daraus folgt `z`{.claim}.
          - Nach k es gilt `x`{.claim}.
          - Nach i es gilt `x -> z`{.claim}.
        - Daraus folgt `t`{.claim}.
          - Nach l es gilt `y`{.claim}.
          - Nach j es gilt `y -> t`{.claim}.
        - Also nach Definition von and (conj), es gilt `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
