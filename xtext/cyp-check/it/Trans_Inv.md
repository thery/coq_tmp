---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: it
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Sia `E : Set`{.var}. Sia `R : Rel E`{.var}. Supponiamo `Trans E R`{.hyp} (h). Dimostriamo `Trans E (Inv E R)`{.claim}.

- Scegliamo arbitrariamente `x y z : E`{.var}; supponiamo `Inv E R x y`{.hyp} (h1) e `Inv E R y z`{.hyp} (h2).
  - Per h abbiamo `Trans E R`{.claim}, cioè `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.fact}.
  - L'elemento `z`{.fact} appartiene a `E`{.fact}.
  - L'elemento `y`{.fact} appartiene a `E`{.fact}.
  - L'elemento `x`{.fact} appartiene a `E`{.fact}.
  - Per h2 abbiamo `Inv E R y z`{.claim}, cioè `R z y`{.fact}.
  - Per h1 abbiamo `Inv E R x y`{.claim}, cioè `R y x`{.fact}.
  - Per applicazione, abbiamo `R z x`{.claim}, cioè `Inv E R x z`{.fact}.
- Abbiamo dimostrato `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`{.claim}, cioè `Trans E (Inv E R)`{.fact}.
