---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

✅ Seien `x y z t : Prop`{.var}. Angenommen `(x -> z) /\ (y -> t)`{.hyp} (h1) und `x /\ y`{.hyp} (h2). Wir zeigen `z /\ t`{.claim}.

- ✅ Zurück zur Definition von and (*and_ind*{.just}) in *h1*{.just}, wir zeigen `z /\ t`{.claim}:
  - ✅ Angenommen `x -> z`{.hyp} (i) und `y -> t`{.hyp} (j). Zurück zur Definition von and (*and_ind*{.just}) in *h2*{.just}, wir zeigen `z /\ t`{.claim}:
    - ✅ Angenommen `x`{.hyp} (k) und `y`{.hyp} (l).
      - ✅ Durch Anwendung von *i*{.just} auf *k*{.just}, es gilt `z`{.claim}.
      - ✅ Durch Anwendung von *j*{.just} auf *l*{.just}, es gilt `t`{.claim}.

      Also nach Definition von and (*conj*{.just}), es gilt `z /\ t`{.claim}.
