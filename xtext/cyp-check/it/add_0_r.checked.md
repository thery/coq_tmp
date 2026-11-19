---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: it
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

✅ Sia `n : nat`{.var}. Dimostriamo `n + 0 = n`{.claim}.

- ✅ Dimostriamo `n + 0 = n` per induzione su `n` (nat, *nat_ind*{.just}):
  - ✅ Caso 1 (base): dimostriamo `0 = 0`{.claim}.
    - ✅ Per definizione di eq (*eq_refl*{.just}), abbiamo `0 = 0`{.claim}.
  - ✅ Caso 2 (induttivo): dimostriamo `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
    - ✅ Scegliamo arbitrariamente `m : nat`{.var}; supponiamo per ipotesi di induzione `m + 0 = m`{.hyp} (IH).
      - ✅ Per definizione di eq (*eq_refl*{.just}), abbiamo `S m = S m`{.claim}.
      - ✅ Per *IH*{.just} abbiamo `m + 0 = m`{.claim}.

      Riscrivendo con `m + 0 = m`{.fact} da destra a sinistra (eq_ind_r), otteniamo `S (m + 0) = S m`{.claim}.

  Essendo questi casi esaustivi, ne deduciamo `n + 0 = n`{.claim}.
