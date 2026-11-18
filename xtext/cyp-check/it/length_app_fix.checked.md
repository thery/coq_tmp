---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: it
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

✅ Dimostriamo `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- ✅ Dimostriamo `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} per ricorsione su `l1`{.fact} (fix length_app'):
  - ▫️ Sia `A : Type`{.var}.
  - ▫️ Siano `l1 l2 : list A`{.var}.
  - ▫️ Dimostriamo `length (l1 ++ l2) = length l1 + length l2`{.fact} per induzione su `l1`{.fact} (list, match):
  - ✅ Caso 1 (base): dimostriamo `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - ✅ Per definizione di eq (eq_refl), abbiamo `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ Caso 2 (induttivo): dimostriamo `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - ▫️ Sia `x : A`{.var}.
    - ▫️ Sia `l : list A`{.var}.
    - ❌ Per ipotesi di induzione (la chiamata ricorsiva length_app') abbiamo `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.

      <details><summary>not proved: forall (A0 : Type) (l10 l20 : list A0),
length (l10 ++ l20) = length l10 + length l20</summary></details>

    - ✅ Usando f_equal otteniamo `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
    - ✅ Ne deduciamo `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - ❌ Essendo questi casi esaustivi, ne deduciamo `length (l1 ++ l2) = length l1 + length l2`{.claim}.

    <details><summary>not proved: length (l1 ++ l2) = length l1 + length l2</summary></details>

