---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: it
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

Dimostriamo `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- Dimostriamo `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} per ricorsione su `l1`{.fact} (fix length_app'):
  - Sia `A : Type`{.var} e `l1 l2 : list A`{.var}.
    - Dimostriamo `length (l1 ++ l2) = length l1 + length l2`{.fact} per induzione su `l1`{.fact} (list, match):
    - Caso 1 (base): dimostriamo `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - Per definizione di eq (eq_refl), abbiamo `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Caso 2 (induttivo): dimostriamo `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - Sia `x : A`{.var} e `l : list A`{.var}.
        - L'elemento `nat`{.fact} appartiene a `Type`{.fact}.
        - L'elemento `nat`{.fact} appartiene a `Type`{.fact}.
        - L'elemento `S`{.fact} appartiene a `nat -> nat`{.fact}.
        - L'elemento `length (l ++ l2)`{.fact} appartiene a `nat`{.fact}.
        - L'elemento `length l + length l2`{.fact} appartiene a `nat`{.fact}.
        - In particolare `length (l ++ l2) = length l + length l2`{.claim}.
          - Per ipotesi di induzione (la chiamata ricorsiva length_app') abbiamo `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
        - Applicando f_equal, abbiamo `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - Essendo questi casi esaustivi, ne deduciamo `length (l1 ++ l2) = length l1 + length l2`{.claim}.
