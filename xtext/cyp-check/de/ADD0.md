---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: de
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Sei `m : nat`{.var}. Wir zeigen `m + 0 = m`{.claim}.

- Um zu zeigen `m + 0 = m`{.fact} durch Induktion (nat, nat_ind), verallgemeinern wir es zu `forall n : nat, n + 0 = n`{.fact}:
- Fall 1 (Anfang): wir zeigen `0 + 0 = 0 + 0`{.claim}.
  - Nach Definition von eq (eq_refl), es gilt `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Fall 2 (Schritt): wir zeigen `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Sei beliebig `m0 : nat`{.var}.
    - Angenommen nach Induktionsvoraussetzung `m0 + 0 = m0`{.hyp} (IH).
      - Nach IH es gilt `m0 + 0 = m0`{.claim}.
      - Mit f_equal wir erhalten `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
      - Daraus folgt `S (m0 + 0) = S m0`{.claim}.
- Da diese Fälle vollständig sind, daraus folgt `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- Insbesondere `m + 0 = m`{.claim}.
