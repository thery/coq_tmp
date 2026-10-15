(******************************************************************************)
(* Tutorial 34 (Omega5): cyclotomic reduction of the roots of unity.          *)
(* omega_n = proot r n (-1) is a primitive 2n-th root of unity on C           *)
(* (UnitArc.v), so it is a root of the cyclotomic polynomial Phi_2n.  After   *)
(* the merging of Tutorial 33 a monomial carries one omega_n ^+ k, but sums   *)
(* such as omega_3 ^+ 2 - omega_3 + 1 are still nonzero normal forms.         *)
(* radcan_check_cyc (Cyclo.v) compares the two normal forms after rewriting   *)
(* every omega_n ^+ k as omega_N ^+ (k N / n), N the lcm of the indices of    *)
(* both sides, and reducing modulo Phi_2N.  Phi_2N is computed over Z         *)
(* (Moebius product) and checked by a certificate:                            *)
(*   p * h = X ^ m - 1, h * g = prod_(q prime | m) (X ^ (m / q) - 1)          *)
(*   + z primitive m-th root of unity  ==>  p (z) = 0     (prim_root_cert)    *)
(* The laws are two records on a negroot w: cycroot w (index law, Omega4) and *)
(* cycprim w (primitivity), with instances rootC_cycroot C, rootC_cycprim C.  *)
(*   radcan_cyc == radcan, then radcan_check_cyc (CycloTac.v)                 *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax.
From Radcan Require Import Radcan Refine Tactic OmegaRoot2 CycC.
From Radcan Require Import Cyclo CycloC CycloTac.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* Phi_m over Z, coefficient of degree 0 first, and its certificate *)
Eval vm_compute in cyclo 10.          (* 1 - X + X^2 - X^3 + X^4 *)
Eval vm_compute in cyc_cert 18.       (* Some (1 - X^3 + X^6) *)

(* the certificate lemma, for any idomain *)
Check @prim_root_cert.

Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Hypotheses (cy : cycroot w) (cp : cycprim w).
Variable x : F.
Local Notation "\w_ n" := (n.-proot (-1)) (at level 3, n at level 2).

(* Phi_6 (omega_3) = 0: was out of reach without the explicit value *)
Lemma g1 : \w_3 ^+ 2 - \w_3 + 1 = 0.
Proof. radcan. Qed.

(* Phi_10 (omega_5) = 0: no explicit value in square roots needed *)
Lemma g2 : \w_5 ^+ 4 - \w_5 ^+ 3 + \w_5 ^+ 2 - \w_5 + 1 = 0.
Proof. radcan. Qed.

(* Phi_18 (omega_9) = 0 *)
Lemma g3 : \w_9 ^+ 6 - \w_9 ^+ 3 + 1 = 0.
Proof. radcan_cyc. Qed.

(* 2 cos (pi / 5) is the golden ratio: t ^+ 2 = t + 1 *)
Lemma g4 : (\w_5 + (\w_5)^-1) ^+ 2 = \w_5 + (\w_5)^-1 + 1.
Proof. radcan_cyc. Qed.

(* 2 cos (pi / 3) = 1 *)
Lemma g5 : \w_3 + (\w_3)^-1 = 1.
Proof. radcan_cyc. Qed.

(* merging (Tutorial 33) and reduction together *)
Lemma g6 : \w_2 * \w_3 = \w_6 ^+ 5.
Proof. radcan_cyc. Qed.

Lemma g7 : \w_8 ^+ 4 = \w_2.
Proof. radcan_cyc. Qed.

(* omega_5 + omega_3 lifted to omega_15, reduced modulo Phi_30 *)
Lemma g8 : \w_5 + \w_3 = \w_15 ^+ 3 + \w_15 ^+ 5.
Proof. radcan_cyc. Qed.

(* with a variable and a real radical as coefficients *)
Lemma g9 : x * \sqrt 2 * (\w_5 ^+ 4 + \w_5 ^+ 2 + 1) =
  x * \sqrt 2 * (\w_5 ^+ 3 + \w_5).
Proof. radcan_cyc. Qed.

(* roots of negative constants (Tutorial 16) feed the same reduction *)
Lemma g10 : 5.-proot (-32) ^+ 4 - 2 * 5.-proot (-32) ^+ 3
  + 4 * 5.-proot (-32) ^+ 2 - 8 * 5.-proot (-32) + 16 = 0.
Proof. radcan_cyc. Qed.

(* a wrong identity is refused *)
Goal \w_7 ^+ 3 + \w_7 = \w_7 ^+ 2.
Proof. Fail radcan_cyc. Abort.
End Generic.

(* On C: n.-root goals, records rootC_cycroot C (CycC.v), rootC_cycprim C *)
Section Complex.
Variable C : numClosedFieldType.

Lemma c1 : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. radcan_cyc. Qed.

Lemma c2 : 5.-root (-1 : C) ^+ 4 - 5.-root (-1) ^+ 3 + 5.-root (-1) ^+ 2
  - 5.-root (-1) + 1 = 0.
Proof. radcan. Qed.

Lemma c3 : 8.-root (-1 : C) ^+ 2 = 4.-root (-1).
Proof. radcan_cyc. Qed.

Lemma c4 : (7.-root (-1 : C) + 11.-root (-1)) ^+ 2 =
  7.-root (-1) ^+ 2 + 2 * 77.-root (-1) ^+ 18 + 11.-root (-1) ^+ 2.
Proof. radcan_cyc. Qed.

(* an omega inside an inverse of a sum is inverted modulo Phi (Tutorial   *)
(* 36); an omega inside a radicand is still an atom, not reduced           *)
Lemma c5 : (1 + 5.-root (-1 : C))^-1 =
  (4 - 3 * 5.-root (-1) + 2 * 5.-root (-1) ^+ 2 - 5.-root (-1) ^+ 3) / 5.
Proof. radcan_cyc. Qed.
End Complex.
