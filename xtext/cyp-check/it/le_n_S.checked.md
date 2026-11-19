---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: it
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ Siano `n m : nat`{.var}. Supponiamo `n <= m`{.hyp} (H). Dimostriamo `S n <= S m`{.claim}.

- ▫️ Dimostriamo `S n <= S m`{.fact} per induzione su `n <= m`{.fact} (H) (le, le_ind):
- ✅ Caso 1 (base): dimostriamo `S n <= S n`{.claim}.
  - ✅ Per definizione di le (le_n), abbiamo `S n <= S n`{.claim} *by Corelib.Init.Peano.le_n*.
- ✅ Caso 2 (induttivo): dimostriamo `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - ▫️ Scegliamo arbitrariamente `m0 : nat`{.var}; supponiamo `n <= m0`{.hyp} (H0) e per ipotesi di induzione `S n <= S m0`{.hyp} (IH).
    - ✅ Per definizione di le (le_S) con testimone `S m0`{.fact}, da `S n <= S m0`{.fact} (IH) ne deduciamo `S n <= S (S m0)`{.claim} *by Corelib.Init.Peano.le_S*.
- ✅ Abbiamo `S n <= S m`{.claim} in tutti i casi.
