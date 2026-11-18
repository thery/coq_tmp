---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

Seien `n m : nat`{.var}. Angenommen `n <= m`{.hyp} (H). Wir zeigen `S n <= S m`{.claim}.

- Wir zeigen `S n <= S m`{.fact} durch Induktion über `n <= m`{.fact} (H) (le, le_ind):
- Fall 1 (Anfang): wir zeigen `S n <= S n`{.claim}.
  - Nach Definition von le (le_n), es gilt `S n <= S n`{.claim} *by Corelib.Init.Peano.le_n*.
- Fall 2 (Schritt): wir zeigen `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - Sei beliebig `m0 : nat`{.var}.
    - Angenommen `n <= m0`{.hyp} (H0) und nach Induktionsvoraussetzung `S n <= S m0`{.hyp} (IH).
      - Nach Definition von le (le_S) mit dem Zeugen `S m0`{.fact}, aus `S n <= S m0`{.fact} (IH) daraus folgt `S n <= S (S m0)`{.claim} *by Corelib.Init.Peano.le_S*.
- Es gilt `S n <= S m`{.claim} in allen Fällen.
