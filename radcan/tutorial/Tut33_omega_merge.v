(******************************************************************************)
(* Tutorial 33 (Omega4): merging roots of unity across indices.               *)
(* In neg mode (Tutorial 16) omega_n = proot r n (-1) is an atom reduced only *)
(* by omega_n ^+ n = -1: omega_4 ^+ 2 and omega_2 are different normal       *)
(* forms.  With the index law of the record cycroot w (OmegaRoot2.v)          *)
(*   wroot w (n * k) ^+ k = wroot w n       (0 < n, 0 < k)                    *)
(* the modes MNegC, MNegCW merge the omega atoms exactly as M5 (Tutorial 11)  *)
(* merges proot n B and proot m B, with no sign condition:                    *)
(*   omega_n ^+ a * omega_m ^+ b = omega_L ^+ (a L/n + b L/m), L = lcm n m    *)
(*   omega_n ^+ k = omega_(n/g) ^+ (k/g),  g = gcd k n > 1                    *)
(* and omega_n ^+ k = - omega_n ^+ (k - n) (n <= k): every monomial carries   *)
(* at most one root of unity, +- omega_n ^+ k with k < n, gcd k n = 1.        *)
(*   radcan_check_negc == MNegC, MNegCW, then radcan_check_neg (Cond.v)       *)
(*   radcan_eq_cond_negc, radcan_eq_refined_negc (NegCyc.v) == its theorems   *)
(*   radcan_negc r w cy == local Ltac: reify, run radcan_check_negc, apply    *)
(*                   radcan_eq_refined_negc                                   *)
(* Omega6: sqrt 2 = w4 - w4 ^+ 3, sqrt 3 = w6 - w6 ^+ 5,                      *)
(* sqrt 5 = 2 w5 - 2 w5 ^+ 4 - 1 (record sqrtroot w, OmegaRoot2.v): in mode   *)
(* MNegS, when the two normal forms differ, the constant square roots of 2,   *)
(* 3, 5 (also inside sqrt 6, sqrt 8, ...) are rewritten into omega atoms, but *)
(* only when the lcm N of the omega indices of the goal is a multiple of 4,   *)
(* 6, 5 resp.; then both sides are simplified again and compared.             *)
(*   radcan_check_negs == MNegS, then radcan_check_negc (Cond.v)              *)
(*   radcan_negs r w cy sq == local Ltac, with radcan_eq_refined_negs         *)
(* First a generic section (w any negroot with a cycroot), then C, where the  *)
(* record is rootC_cycroot C (CycC.v, from the index law of UnitArc.v).       *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax.
From Radcan Require Import Radcan Refine Tactic OmegaRoot2 NegCyc CycC.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* radcan_with_gen of Tactic.v, with radcan_check_negc *)
Ltac radcan_negc r w cy :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let c := eval vm_compute in (radcan_check_negc e1 e2) in
      lazymatch c with
      | Some ?cs =>
          let rcs := eval vm_compute in (refine cs) in
          apply: (@radcan_eq_refined_negc _ r w cy env e1 e2 cs rcs);
          [radcan_vm_refl | radcan_vm_refl | radcan_split_rconds]
      | None => fail "radcan_negc: the normal forms differ"
      end
  end.

Section Merge.

Variables (F : numFieldType) (r : posroot F) (w : negroot r).
Hypothesis cy : cycroot w.

Local Notation om n := (proot r n (-1)).

(* without the index law the plain neg mode fails *)
Goal om 4 ^+ 2 = om 2.
Proof. Fail radcan_with_gen true r w. radcan_negc r w cy. Qed.

(* the gcd rule *)
Goal om 6 ^+ 2 = om 3.
Proof. radcan_negc r w cy. Qed.

Goal om 12 ^+ 3 = om 4.
Proof. radcan_negc r w cy. Qed.

Goal om 8 ^+ 4 = om 2.
Proof. radcan_negc r w cy. Qed.

(* the lcm rule: omega_2 omega_3 = omega_6 ^+ (3 + 2) *)
Goal om 2 * om 3 = om 6 ^+ 5.
Proof. radcan_negc r w cy. Qed.

(* omega_6 omega_3 = omega_6 ^+ 3 = omega_2 *)
Goal om 6 * om 3 = om 2.
Proof. radcan_negc r w cy. Qed.

(* then omega_n ^+ n = -1: omega_4 ^+ 3 omega_12 ^+ 5 = omega_12 ^+ 14 *)
Goal om 4 ^+ 3 * om 12 ^+ 5 = - om 6.
Proof. radcan_negc r w cy. Qed.

(* inverses: omega_n ^-1 = - omega_n ^+ (n - 1) *)
Goal (om 4)^-1 * om 2 = om 4.
Proof. radcan_negc r w cy. Qed.

(* with real radicals and variables (x != 0 for the inverse) *)
Goal forall x : F, x != 0 ->
  (proot r 2 2 * om 4 * x) ^+ 2 / x = 2 * om 2 * x.
Proof. move=> x x0; radcan_negc r w cy; exact: x0. Qed.

(* roots of negative constants: proot r n (- a) = proot r n a * omega_n *)
Goal proot r 4 (-4) ^+ 2 = proot r 2 (-4).
Proof. radcan_negc r w cy. Qed.

End Merge.

Section OnC.

Variable C : numClosedFieldType.

Ltac radcan_negcC :=
  radcan_negc (rootC_posroot C) (rootC_negroot C) (rootC_cycroot C).

Goal 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. radcan_negcC. Qed.

Goal 6.-root (-1 : C) ^+ 2 = 3.-root (-1).
Proof. radcan_negcC. Qed.

Goal 2.-root (-1 : C) * 3.-root (-1) = 6.-root (-1) ^+ 5.
Proof. radcan_negcC. Qed.

Goal 12.-root (-1 : C) ^+ 3 = 4.-root (-1).
Proof. radcan_negcC. Qed.

(* beyond the explicit values of Omega2 (2 n | 24): radcan itself now uses
   the cycroot mode on n.-root goals *)
Goal 10.-root (-1 : C) ^+ 2 = 5.-root (-1).
Proof. radcan. Qed.

Goal 8.-root (-1 : C) ^+ 2 * 5.-root (-1) = 20.-root (-1) ^+ 9.
Proof. radcan. Qed.

End OnC.

(* Omega6 *)
Ltac radcan_negs r w cy sq :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let c := eval vm_compute in (radcan_check_negs e1 e2) in
      lazymatch c with
      | Some ?cs =>
          let rcs := eval vm_compute in (refine cs) in
          apply: (@radcan_eq_refined_negs _ r w cy sq env e1 e2 cs rcs);
          [radcan_vm_refl | radcan_vm_refl | radcan_split_rconds]
      | None => fail "radcan_negs: the normal forms differ"
      end
  end.

Section Sqrt.

Variables (F : numFieldType) (r : posroot F) (w : negroot r).
Hypotheses (cy : cycroot w) (sq : sqrtroot w).

Local Notation om n := (proot r n (-1)).

Goal om 4 + (om 4)^-1 = proot r 2 2.
Proof. radcan_negs r w cy sq. Qed.

(* sqrt 6 = sqrt 2 sqrt 3, with omega_4 and omega_6 present *)
Goal proot r 2 6 = (om 4 - om 4 ^+ 3) * (om 6 - om 6 ^+ 5).
Proof. radcan_negs r w cy sq. Qed.

End Sqrt.

Section SqrtC.

Variable C : numClosedFieldType.

Ltac radcan_negsC :=
  radcan_negs (rootC_posroot C) (rootC_negroot C) (rootC_cycroot C)
    (rootC_sqrtroot C).

Goal 4.-root (-1 : C) + (4.-root (-1))^-1 = 2.-root 2.
Proof. radcan_negsC. Qed.

Goal 6.-root (-1 : C) - 6.-root (-1) ^+ 5 = 2.-root 3.
Proof. radcan_negsC. Qed.

(* beyond the explicit values of Omega2: radcan itself now uses mode MNegS *)
Goal 2 * 5.-root (-1 : C) - 2 * 5.-root (-1) ^+ 4 - 1 = 2.-root 5.
Proof. radcan. Qed.

(* 2 cos (pi / 5) = omega_5 + omega_5 ^-1 is the golden ratio *)
Goal 10.-root (-1 : C) ^+ 2 + (5.-root (-1))^-1 = (2.-root 5 + 1) / 2.
Proof. radcan. Qed.

Goal 8.-root (-1 : C) ^+ 2 + (8.-root (-1)) ^- 2 = 2.-root 2.
Proof. radcan. Qed.

Goal forall x : C,
  2.-root 8 * x = 2 * (4.-root (-1) - 4.-root (-1) ^+ 3) * x.
Proof. move=> x; radcan_negsC. Qed.

(* no omega_4 in the goal: sqrt 2 is not rewritten *)
Goal 2.-root (2 : C) * 2.-root (-1) = 2.-root (-2).
Proof. radcan_negsC. Qed.

End SqrtC.
