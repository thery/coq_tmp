---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ Siano `n m : nat`{.var}. Supponiamo `n <= m`{.hyp} (H). Dimostriamo `S n <= S m`{.claim}.

- ✅ Dimostriamo `S n <= S m` per induzione su *H*{.just} (*le*{.just}, *induction*{.just}):
  - ✅ Caso 1 (base): dimostriamo `S n <= S n`{.claim}.
    - ✅ Per definizione di le (*le_n*{.just}), abbiamo `S n <= S n`{.claim}.
  - ✅ Caso 2 (induttivo): dimostriamo `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
    - ✅ Scegliamo arbitrariamente `m0 : nat`{.var}; supponiamo `n <= m0`{.hyp} (H0) e per ipotesi di induzione `S n <= S m0`{.hyp} (IH). Per definizione di le (*le_S*{.just}) con testimone `S m0`, da *IH*{.just} ne deduciamo `S n <= S (S m0)`{.claim}.

  Abbiamo `S n <= S m`{.claim} in tutti i casi.
