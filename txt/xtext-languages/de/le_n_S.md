---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

Seien `n m : nat`{.var}. Angenommen `n <= m`{.hyp} (H). Wir zeigen `S n <= S m`{.claim}.

- Wir zeigen `S n <= S m` durch Induktion über *H*{.just} (le, le_ind):
  - Fall 1 (Anfang): wir zeigen `S n <= S n`{.claim}.
    - Nach Definition von le (*le_n*{.just}), es gilt `S n <= S n`{.claim}.
  - Fall 2 (Schritt): wir zeigen `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
    - Seien beliebig `m0 : nat`{.var}; angenommen `n <= m0`{.hyp} (H0) und nach Induktionsvoraussetzung `S n <= S m0`{.hyp} (IH). Nach Definition von le (*le_S*{.just}) mit dem Zeugen `S m0`, aus *IH*{.just} daraus folgt `S n <= S (S m0)`{.claim}.

  Es gilt `S n <= S m`{.claim} in allen Fällen.
