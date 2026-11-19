---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: it
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Sia `m : nat`{.var}. Dimostriamo `m + 0 = m`{.claim}.

- Dimostriamo `m + 0 = m`{.fact} per induzione su `m`{.fact} (nat, nat_ind):
- Caso 1 (base): dimostriamo `0 + 0 = 0 + 0`{.claim}.
  - Per definizione di eq (eq_refl), abbiamo `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Caso 2 (induttivo): dimostriamo `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Scegliamo arbitrariamente `m0 : nat`{.var}; supponiamo per ipotesi di induzione `m0 + 0 = m0`{.hyp} (IH).
    - L'elemento `nat`{.fact} appartiene a `Type`{.fact}.
    - L'elemento `nat`{.fact} appartiene a `Type`{.fact}.
    - L'elemento `S`{.fact} appartiene a `nat -> nat`{.fact}.
    - L'elemento `m0 + 0`{.fact} appartiene a `nat`{.fact}.
    - L'elemento `m0`{.fact} appartiene a `nat`{.fact}.
    - Per IH abbiamo `m0 + 0 = m0`{.claim}.
    - Applicando f_equal, abbiamo `S (m0 + 0) = S m0`{.claim}.
- Essendo questi casi esaustivi, ne deduciamo `m + 0 = m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
