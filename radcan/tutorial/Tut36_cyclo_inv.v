(******************************************************************************)
(* Tutorial 36: inverses of sums of roots of unity.                           *)
(* In Tutorial 34 the inverse of a sum such as 1 + omega_5 stays an opaque    *)
(* atom AInv (1 + omega_5).  radcan_check_cyc2 (CycloInv.v), the checker of   *)
(* radcan with the records cycroot w and cycprim w (Dispatch.v), replaces     *)
(* such an atom AInv q by a polynomial v in omega_N, N the lcm of the omega   *)
(* indices of q, before the cyclotomic reduction of Tutorial 34:              *)
(* - q free of variables (rationals, omegas, constant real radicals): v is    *)
(*   computed by linear algebra over Q (cyc_inv_cand, unverified), then       *)
(*   q * v is reduced modulo Phi_2N and compared with 1.  From q * v = 1 we   *)
(*   get q^-1 = v (mulr1_inv) with no side condition q != 0: q * v = 1        *)
(*   already implies q != 0 (mulr1_neq0).  For the same reason a condition    *)
(*   q != 0 left by the normaliser is dropped (cyc_cfilter).                  *)
(* - otherwise (variables): P = the product of the conjugates of q            *)
(*   (omega_N -> omega_N ^+ a, a prime to 2N, a <> 1), n = q * P reduced      *)
(*   modulo Phi_2N; when n is free of omegas (checked: q * P = n) then        *)
(*   q^-1 = P * n^-1 under the side condition n != 0 (cyc_inv_norm).          *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax.
From Radcan Require Import Radcan Refine Tactic OmegaRoot2 CycC.
From Radcan Require Import Cyclo CycloC CycloInv.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* the two facts behind the check *)
Check @mulr1_neq0.
Check @mulr1_inv.

(* the candidate inverse of 1 + omega_5, computed modulo Phi_10 *)
Eval vm_compute in
  cyc_inv_cand (RadcanZ.pnorm (RAdd (RCst 1) (RRootE 5 (RCst (-1))))).

Section Complex.
Variable C : numClosedFieldType.

(* the goal refused in Tutorial 34 *)
Lemma i1 : (1 + 5.-root (-1 : C))^-1 =
  (4 - 3 * 5.-root (-1) + 2 * 5.-root (-1) ^+ 2 - 5.-root (-1) ^+ 3) / 5.
Proof. Time radcan. Qed.

(* modulo Phi_6 = X ^ 2 - X + 1 *)
Lemma i2 : 1 / (1 + 3.-root (-1 : C)) = (2 - 3.-root (-1)) / 3.
Proof. Time radcan. Qed.

(* a cubic in omega_7, inverted modulo Phi_14 *)
Lemma i3 : 1 / (7.-root (-1 : C) - 7.-root (-1) ^+ 3 + 2) =
  (20 - 15 * 7.-root (-1) + 9 * 7.-root (-1) ^+ 2 + 4 * 7.-root (-1) ^+ 3
   - 8 * 7.-root (-1) ^+ 4 + 7 * 7.-root (-1) ^+ 5) / 29.
Proof. Time radcan. Qed.

(* mixed with the real radical sqrt 2 *)
Lemma i4 : 1 / (2.-root 2 + 4.-root (-1 : C)) =
  (2 * 2.-root 2 - 2 * 4.-root (-1) + 2.-root 2 * 4.-root (-1) ^+ 2
   - 4.-root (-1) ^+ 3) / 5.
Proof. Time radcan. Qed.

(* inverses on both sides, and a power of an inverse *)
Lemma i5 : (1 + 5.-root (-1 : C))^-1 * (1 - 5.-root (-1))^-1 =
  (1 - 5.-root (-1) ^+ 2)^-1.
Proof. Time radcan. Qed.

Lemma i6 : ((1 + 3.-root (-1 : C))^-1) ^+ 6 = -1 / 27.
Proof. Time radcan. Qed.

(* omega_3 and omega_5 together: inverted modulo Phi_30 *)
Lemma i7 : (3.-root (-1 : C) + 5.-root (-1))^-1 *
  (3.-root (-1) + 5.-root (-1)) = 1.
Proof. Time radcan. Qed.

(* the normaliser cancels 1 + omega_5 under the side condition             *)
(* 1 + omega_5 != 0, dropped since 1 + omega_5 has a checked inverse        *)
Variable x : C.
Lemma i8 : x / (1 + 5.-root (-1)) * (1 + 5.-root (-1)) = x.
Proof. Time radcan. Qed.

(* with a variable: the norm x ^+ 2 + x + 1 of x + omega_3 must be nonzero *)
Lemma i9 : x ^+ 2 + x + 1 != 0 ->
  1 / (x + 3.-root (-1)) = (x + 1 - 3.-root (-1)) / (x ^+ 2 + x + 1).
Proof.
(* the refined side condition is x + x ^+ 2 != -1 *)
move=> hx; radcan; by rewrite -addr_eq0 [x + _]addrC.
Qed.

(* wrong identities are refused *)
Goal (1 + 5.-root (-1 : C))^-1 =
  (4 - 3 * 5.-root (-1) + 2 * 5.-root (-1) ^+ 2 - 5.-root (-1) ^+ 3) / 3.
Proof. Fail radcan. Abort.

Goal 1 / (x + 3.-root (-1 : C)) = (x + 3.-root (-1)) / (x ^+ 2 + x + 1).
Proof. Fail radcan. Abort.
End Complex.

(* any posroot with the two records on a negroot w *)
Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r).
Hypotheses (cy : cycroot w) (cp : cycprim w).
Local Notation "\w_ n" := (proot r n (-1)) (at level 3, n at level 2).

Lemma g1 : (1 + \w_5)^-1 =
  (4 - 3 * \w_5 + 2 * \w_5 ^+ 2 - \w_5 ^+ 3) / 5.
Proof. Time radcan. Qed.

Lemma g2 : (1 + \w_3)^-1 * (2 - \w_3) = (2 - \w_3) ^+ 2 / 3.
Proof. Time radcan. Qed.
End Generic.
