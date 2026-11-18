---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Sia `n : nat`{.var}. Dimostriamo `n + 0 = n`{.claim}.

- Per dimostrare `n + 0 = n`{.fact} per induzione (nat, nat_ind), lo generalizziamo in `forall n0 : nat, n0 + 0 = n0`{.fact}:
- Caso 1 (base): dimostriamo `0 = 0`{.claim}.
  - Per definizione di eq (eq_refl), abbiamo `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Caso 2 (induttivo): dimostriamo `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - Scegliamo arbitrariamente `m : nat`{.var}; supponiamo per ipotesi di induzione `m + 0 = m`{.hyp} (IH).
    - Per definizione di eq (eq_refl), abbiamo `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Per IH abbiamo `m + 0 = m`{.claim}.
    - Riscrivendo con `m + 0 = m`{.fact} da destra a sinistra (eq_ind_r), otteniamo `S (m + 0) = S m`{.claim}.
- Essendo questi casi esaustivi, ne deduciamo `forall n0 : nat, n0 + 0 = n0`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- In particolare `n + 0 = n`{.claim}.
