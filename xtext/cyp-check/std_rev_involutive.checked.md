---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# rev_involutive

✅ Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `rev (rev l) = l`{.claim}.

- ✅ We prove `rev (rev l) = l` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - ✅ Case 1 (base): we prove `nil = (@nil A)`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `nil = (@nil A)`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), rev (rev l0) = l0 -> rev (rev (a :: l0)) = a :: l0`{.claim}.
    - ✅ Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `rev (rev l0) = l0`{.hyp} (IHl).
      - ✅ Rewriting with `rev (rev l0) = l0`{.fact} from right to left (eq_ind_r), we get `a :: rev (rev l0) = a :: l0`{.claim}.
        - ✅ By definition of eq (*eq_refl*{.just}), we have `a :: l0 = a :: l0`{.claim}.
        - ✅ By *IHl*{.just} we have `rev (rev l0) = l0`{.claim}.
      - ✅ Applying *List.rev_unit*{.just}, we have `rev (rev l0 ++ a :: nil) = a :: rev (rev l0)`{.claim}.
        - ▫️ The element `rev l0` belongs to `list A`.

      Rewriting with `rev (rev l0 ++ a :: nil) = a :: rev (rev l0)`{.fact} from right to left (eq_ind_r), we get `rev (rev l0 ++ a :: nil) = a :: l0`{.claim}.

  These cases being exhaustive, we deduce `rev (rev l) = l`{.claim}.
