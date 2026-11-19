---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Sia `E : Set`{.var}. Sia `R : Rel E`{.var}. Supponiamo `Trans E R`{.hyp} (h). Dimostriamo `Trans E (Inv E R)`{.claim}.

- Scegliamo arbitrariamente `x y z : E`{.var}; supponiamo `Inv E R x y`{.hyp} (h1) e `Inv E R y z`{.hyp} (h2).
  - Per *h*{.just} abbiamo `Trans E R`, cioè `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`{.claim}.
  - Per *h2*{.just} abbiamo `Inv E R y z`, cioè `R z y`{.claim}.
  - Per *h1*{.just} abbiamo `Inv E R x y`, cioè `R y x`{.claim}.

  Per applicazione, abbiamo `R z x`, cioè `Inv E R x z`{.claim}.
- Abbiamo dimostrato `forall x0 y0 z0 : E, Inv E R x0 y0 -> Inv E R y0 z0 -> Inv E R x0 z0`, cioè `Trans E (Inv E R)`{.claim}.
