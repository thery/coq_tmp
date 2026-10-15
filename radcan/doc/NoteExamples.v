(* Every Rocq example quoted in radcan-note.typ, checked. *)
From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot PosRootFacts RootC RootR RealRoot.
From Radcan Require Import Syntax Radcan Refine Tactic RootRstd Sym SymTac.
From Radcan Require Import UnitArc RootComp GaussSum Cyclo.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).

Lemma sqrt2_sqrt3 : proot r 2 2 * proot r 2 3 = proot r 2 6.
Proof. by rewrite -prootM // -natrM. Qed.

Lemma g1 : proot r 2 2 * proot r 2 3 = proot r 2 6. Proof. radcan. Qed.
Lemma g2 : (1 + proot r 2 2) ^+ 2 = 3 + 2 * proot r 2 2. Proof. radcan. Qed.
Lemma g3 : proot r 2 8 = 2 * proot r 2 2. Proof. radcan. Qed.
Lemma g4 : proot r 3 2 * proot r 2 2 = proot r 6 32. Proof. radcan. Qed.
Lemma g5 : proot r 2 12 - proot r 2 3 = proot r 2 3. Proof. radcan. Qed.

Lemma d2 : 1 / (1 + proot r 2 2) = proot r 2 2 - 1. Proof. radcan. Qed.
Lemma d5 : 1 / (1 + proot r 2 2 + proot r 2 3) =
           (2 + proot r 2 2 - proot r 2 6) / 4.
Proof. radcan. Qed.

Lemma v4 : (x - y * proot r 2 3) * (x + y * proot r 2 3) = x ^+ 2 - 3 * y ^+ 2.
Proof. radcan. Qed.

Lemma c1 : 0 <= x -> proot r 2 (x ^+ 2) = x.
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.

Lemma f1 : 1 < x ->
  proot r 2 (x ^+ 2 - 1) / proot r 2 (x - 1) = proot r 2 (x + 1).
Proof. move=> h. radcan. exact: h. Qed.

Lemma dn1 : proot r 2 (3 + 2 * proot r 2 2) = 1 + proot r 2 2.
Proof. radcan. Qed.

Lemma m1 : proot r 2 (10 + 2 * proot r 2 6 + 2 * proot r 2 10
                         + 2 * proot r 2 15)
         = proot r 2 2 + proot r 2 3 + proot r 2 5.
Proof. radcan. Qed.
End Generic.

Lemma cc1 (C : numClosedFieldType) : (3.-root 2) * (2.-root 2) = 6.-root 32 :> C.
Proof. radcan. Qed.

Lemma u2 (C : numClosedFieldType) : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. by radcan. Qed.

Lemma u10 (C : numClosedFieldType) : 5.-root (-1 : C) ^+ 4 - 5.-root (-1) ^+ 3
          + 5.-root (-1) ^+ 2 - 5.-root (-1) + 1 = 0.
Proof. by radcan. Qed.

(* the theorems of the section "Some theorems proved on the way" *)
Check rootC_N1_prim : forall (C : numClosedFieldType) n, (0 < n)%N ->
  (2 * n).-primitive_root (n.-root (-1 : C)).
Check rootC_N1_index : forall (C : numClosedFieldType) n k,
  (0 < n)%N -> (0 < k)%N -> (n * k).-root (-1 : C) ^+ k = n.-root (-1).
Check @rootC_mul.
Check @gauss_sumC.
Check @prim_root_cert.

Section Real.
Variables (R : rcfType) (x : R).
Lemma a1 : rootR 2 ((x - 2) ^+ 2) = `|x - 2|.  Proof. by radcan. Qed.
Lemma o2 : rootR 3 (- 8 * x ^+ 3) = - 2 * x.   Proof. by radcan. Qed.
End Real.

Section Paper2.
Variables (F : numFieldType) (x u w z : F).
Hypotheses (hu : u ^+ 4 = x - 1) (hw : w ^+ 4 = -1) (hz : z = w * u).

Lemma paper2 : x != 1 ->
  u / z - u ^+ 3 / z ^+ 3 - (w - w ^+ 3) = 0.
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.
End Paper2.

Local Open Scope R_scope.
Lemma l3 : sqrt 12 - sqrt 3 = sqrt 3.
Proof. radcan_lra. Qed.

Lemma l1 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> h. radcan_lra. Qed.

Lemma b1 : sqrt (1000000007 ^ 2 * 3) = 1000000007 * sqrt 3.
Proof. radcan_Rstd. radcan. Qed.
