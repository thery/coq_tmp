---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: it
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Sia `m : nat`{.var}. Dimostriamo `m + 0 = m`{.claim}.

- ▫️ Per dimostrare `m + 0 = m`{.fact} per induzione (nat, nat_ind), lo generalizziamo in `forall n : nat, n + 0 = n`{.fact}:
- ✅ Caso 1 (base): dimostriamo `0 + 0 = 0 + 0`{.claim}.
  - ✅ Per definizione di eq (eq_refl), abbiamo `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Caso 2 (induttivo): dimostriamo `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - ▫️ Consideriamo un elemento arbitrario `m0 : nat`{.var}.
    - ▫️ Supponiamo per ipotesi di induzione `m0 + 0 = m0`{.hyp} (IH).
      - ✅ Per IH abbiamo `m0 + 0 = m0`{.claim}.
      - ✅ Usando f_equal otteniamo `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
      - ✅ Ne deduciamo `S (m0 + 0) = S m0`{.claim}.
- ✅ Essendo questi casi esaustivi, ne deduciamo `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- ✅ In particolare `m + 0 = m`{.claim}.
