(******************************************************************************)
(* Tutorial 27: explicit values of the roots of unity omega_n = n.-root (-1)  *)
(* on C for 2n | 24 (OmegaC.v), and the record smallroot (OmegaRoot.v).      *)
(*   mathcomp's n.-root x is the root of X^n - x in the closed upper          *)
(*   half-plane with the largest real part, so omega_n = exp (i pi / n).      *)
(*   rootC_char characterises it; rootC_double gives                          *)
(*   (2 * n).-root x = sqrtC (n.-root x).                                     *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC OmegaRoot OmegaC.
From Radcan Require Import Syntax Radcan Refine Tactic NegRootC.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Omega.
Variable C : numClosedFieldType.

(* the explicit values, in Q(i, sqrt 2, sqrt 3) *)
Check omega1C C : 1.-root (-1 : C) = -1.
Check omega2C C : 2.-root (-1 : C) = 'i.
Check omega3C C : 3.-root (-1 : C) = (1 + sqrtC 3 * 'i) / 2.
Check omega4C C : 4.-root (-1 : C) = sqrtC 2 / 2 * (1 + 'i).
Check omega6C C : 6.-root (-1 : C) = (sqrtC 3 + 'i) / 2.
Check omega12C C : 12.-root (-1 : C) =
  ((sqrtC 6 + sqrtC 2) + (sqrtC 6 - sqrtC 2) * 'i) / 4.

(* the characterisation used to prove them *)
Check @rootC_char C.
Check @rootC_double C.

(* cyclotomic and index relations, proved in OmegaC.v *)
Check omega3_cycloC C : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Check omega4_sqrC C : 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Check omega4_sqrt2C C : 4.-root (-1 : C) - 4.-root (-1) ^+ 3 = sqrtC 2.
Check omega4_invC C : 4.-root (-1 : C) + (4.-root (-1))^-1 = sqrtC 2.
Check omega6_sqrC C : 6.-root (-1 : C) ^+ 2 = 3.-root (-1).
Check omega6_cubeC C : 6.-root (-1 : C) ^+ 3 = 'i.
Check omega12_sqrC C : 12.-root (-1 : C) ^+ 2 = 6.-root (-1).
Check omega12_cubeC C : 12.-root (-1 : C) ^+ 3 = 4.-root (-1).

(* radcan alone does not see these relations (Tutorial 16); after
   unfolding the explicit values (and 'i back into 2.-root (-1)) it does *)
Lemma o1 : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. by rewrite omega3C -omega2C; radcan. Qed.

Lemma o2 : 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. by rewrite omega4C -omega2C; radcan. Qed.

Lemma o3 : 12.-root (-1 : C) ^+ 3 = 4.-root (-1).
Proof. by rewrite omega12C omega4C -omega2C; radcan. Qed.

(* paper eq. (2), second reading *)
Lemma o4 : (4.-root (-1 : C))^-1 - (4.-root (-1))^-1 ^+ 3 - sqrtC 2 = 0.
Proof. by rewrite omega4C -omega2C; radcan. Qed.

End Omega.

(* the record, with its instance on C *)
Check @smallroot.
Check fun C : numClosedFieldType => rootC_smallroot C.
