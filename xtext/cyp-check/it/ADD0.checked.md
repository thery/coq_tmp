---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: it
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Sia `m : nat`{.var}. Dimostriamo `m + 0 = m`{.claim}.

- ✅ Dimostriamo `m + 0 = m` per induzione su `m` (nat, *nat_ind*{.just}):
  - ✅ Caso 1 (base): dimostriamo `0 + 0 = 0 + 0`{.claim}.
    - ✅ Per definizione di eq (*eq_refl*{.just}), abbiamo `0 + 0 = 0 + 0`{.claim}.
  - ✅ Caso 2 (induttivo): dimostriamo `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - ✅ Scegliamo arbitrariamente `m0 : nat`{.var}; supponiamo per ipotesi di induzione `m0 + 0 = m0`{.hyp} (IH).
      - ▫️ L'elemento `nat` appartiene a `Type`.
      - ▫️ L'elemento `nat` appartiene a `Type`.
      - ▫️ L'elemento `S` appartiene a `nat -> nat`.
      - ▫️ L'elemento `m0 + 0` appartiene a `nat`.
      - ✅ Per *IH*{.just} abbiamo `m0 + 0 = m0`{.claim}.

      Applicando *f_equal*{.just}, abbiamo `S (m0 + 0) = S m0`{.claim}.

  Essendo questi casi esaustivi, ne deduciamo `m + 0 = m`{.claim}.
