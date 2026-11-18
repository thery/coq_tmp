---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: it
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

✅ Siano `n m : nat`{.var}. Dimostriamo `S (n + m) = n + S m`{.claim}.

- ▫️ Per dimostrare `S (n + m) = n + S m`{.fact} per induzione (nat, nat_ind), lo generalizziamo in `forall n0 : nat, S (n0 + m) = n0 + S m`{.fact}:
- ✅ Caso 1 (base): dimostriamo `0 + S m = 0 + S m`{.claim}.
  - ✅ Per definizione di eq (eq_refl), abbiamo `0 + S m = 0 + S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Caso 2 (induttivo): dimostriamo `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
  - ▫️ Consideriamo un elemento arbitrario `n0 : nat`{.var}.
    - ▫️ Supponiamo per ipotesi di induzione `S (n0 + m) = n0 + S m`{.hyp} (IH).
      - ✅ Per definizione di eq (eq_refl), abbiamo `S (n0 + S m) = S (n0 + S m)`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - ✅ Per IH abbiamo `S (n0 + m) = n0 + S m`{.claim}.
      - ✅ Riscrivendo con `S (n0 + m) = n0 + S m`{.fact} da destra a sinistra (eq_ind_r), otteniamo `S (S (n0 + m)) = S (n0 + S m)`{.claim}.
- ✅ Essendo questi casi esaustivi, ne deduciamo `forall n0 : nat, S (n0 + m) = n0 + S m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- ✅ In particolare `S (n + m) = n + S m`{.claim}.
