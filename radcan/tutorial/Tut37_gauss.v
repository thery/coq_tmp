(******************************************************************************)
(* Tutorial 37: every square root of a positive integer as a sum of roots of  *)
(* -1 (quadratic Gauss sums); it replaces the former table of sqrt 2, 3, 5    *)
(* (Omega6).  With wn = omega_n = proot r n (-1) (= e^(i pi / n) on C):       *)
(*   sqrt 2 = w4 - w4 ^+ 3                                                    *)
(*   sqrt n = sum_(a < n) wn ^+ (2 a^2 mod 2n)              (n = 1 mod 4)     *)
(*   sqrt n = sum_(a < n) w2n ^+ ((3n + 4 a^2) mod 4n)      (n = 3 mod 4)     *)
(* (GaussSum.v on C, any n, not only primes).  They are the fields of the     *)
(* record gaussroot w (GaussMode.v), instance rootC_gaussroot C (GaussC.v).   *)
(* radcan_check_gauss: the normal forms of modes MNegC, MNegCW; when they     *)
(* differ, the constant square roots are substituted and both sides are       *)
(* compared after the cyclotomic reduction modulo Phi_2N (Tutorial 34).       *)
(* Trigger rule, N = lcm of the omega indices of the two normal forms, gidx b *)
(* = the index of the sum of sqrt b (b = 2^k m, m odd: lcm of 4 if k is odd   *)
(* and m if m = 1 mod 4, 2m otherwise):                                       *)
(*   in each term, the product B of the constant square roots is replaced by  *)
(*   its sum when gidx B | N, else each sqrt b with gidx b | N is replaced.   *)
(* So no omega of a new index appears: the cyclotomic field of the goal, and  *)
(* the size of the reduction, stay those of the goal; a goal without omega    *)
(* atoms is never rewritten.  The mode is tried by radcan (Dispatch.v) only   *)
(* when the cyclotomic checker fails, so the goals proved before keep their   *)
(* proofs and conditions.                                                     *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax.
From Radcan Require Import Radcan Refine Tactic OmegaRoot2 Cyclo GaussMode.
From Radcan Require Import GaussC.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* the substitution of sqrt 21 in a term, and the trigger index *)
Eval vm_compute in (gidx 7%positive, gidx 21%positive, gidx 14%positive).
(* = (14, 21, 28) *)

(* any negroot with the index law, primitivity and the Gauss sums *)
Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Hypotheses (cy : cycroot w) (cp : cycprim w) (gs : gaussroot w).
Local Notation "\w_ n" := (n.-proot (-1)) (at level 3, n at level 2).

(* sqrt 7 with the 14-th roots of -1 (exponents 21, 25, 9, 1, 1, 9, 25) *)
Lemma g1 : \sqrt 7 = \w_14 ^+ 21 + 2 * \w_14 ^+ 25 + 2 * \w_14 ^+ 9
  + 2 * \w_14.
Proof. Time radcan. Qed.

(* 2 cos (2 pi / 5) = (sqrt 5 - 1) / 2 *)
Lemma g2 : \w_5 ^+ 2 + (\w_5) ^- 2 = (\sqrt 5 - 1) / 2.
Proof. Time radcan. Qed.

(* the golden ratio, 2 cos (pi / 5) *)
Lemma g3 : \w_5 + (\w_5)^-1 = (\sqrt 5 + 1) / 2.
Proof. Time radcan. Qed.

(* sqrt 13 with a variable as coefficient *)
Lemma g4 (x : F) : x * \sqrt 13 =
  x * \sum_(a < 13) \w_13 ^+ ((a * a).*2 %% 26).
Proof. rewrite !big_ord_recr big_ord0 /=. Time radcan. Qed.

(* a wrong coefficient is refused *)
Goal \sqrt 7 = \w_14 ^+ 21 + 2 * \w_14 ^+ 25 + 2 * \w_14 ^+ 9 + \w_14.
Proof. Fail radcan. Abort.

End Generic.

(* without the record gaussroot w, the cyclotomic checker alone fails *)
Section NoGauss.
Variables (F : numFieldType) (r : posroot F) (w : negroot r).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Hypotheses (cy : cycroot w) (cp : cycprim w).
Local Notation "\w_ n" := (n.-proot (-1)) (at level 3, n at level 2).

Goal \w_5 ^+ 2 + (\w_5) ^- 2 = (\sqrt 5 - 1) / 2.
Proof. Fail radcan. Abort.
End NoGauss.

(* the decision theorems use no axiom *)
Print Assumptions radcan_eq_cond_gauss.
Print Assumptions rootC_gaussroot.

(* On C: plain radcan, n.-root goals *)
Section Complex.
Variable C : numClosedFieldType.

(* sqrt 7 = sum_(a < 7) omega_14 ^+ ((21 + 4 a^2) mod 28) (sqrtC7_root) *)
Lemma c1 : 2.-root (7 : C) =
  \sum_(a < 7) 14.-root (-1 : C) ^+ ((7 * 3 + a * a * 4) %% (7 * 4)).
Proof. rewrite !big_ord_recr big_ord0 /=. Time radcan. Qed.

(* the same with the powers written out *)
Lemma c2 : 2.-root (7 : C) = 14.-root (-1) ^+ 21 + 2 * 14.-root (-1) ^+ 25
  + 2 * 14.-root (-1) ^+ 9 + 2 * 14.-root (-1).
Proof. Time radcan. Qed.

(* i sqrt 7 is the Gauss sum of the 7-th roots of unity omega_7 ^+ 2 *)
Lemma c3 : 2.-root (-7 : C) = \sum_(a < 7) 7.-root (-1 : C) ^+ ((a * a).*2).
Proof. rewrite !big_ord_recr big_ord0 /=. Time radcan. Qed.

(* sqrt 3 sqrt 7 = sqrt 21, as a sum of omega_21 (product rule) *)
Lemma c4 : 2.-root (3 : C) * 2.-root 7 =
  \sum_(a < 21) 21.-root (-1 : C) ^+ ((a * a).*2 %% 42).
Proof. rewrite !big_ord_recr big_ord0 /=. Time radcan. Qed.

(* sqrt 14 = sqrt 2 sqrt 7 with omega_4 and omega_14 (N = 28) *)
Lemma c5 : 2.-root (14 : C) = (4.-root (-1) - 4.-root (-1) ^+ 3) *
  (14.-root (-1) ^+ 21 + 2 * 14.-root (-1) ^+ 25
   + 2 * 14.-root (-1) ^+ 9 + 2 * 14.-root (-1)).
Proof. Time radcan. Qed.

(* 2 cos (2 pi / 5) and the golden ratio *)
Lemma c6 : 5.-root (-1 : C) ^+ 2 + (5.-root (-1)) ^- 2 = (2.-root 5 - 1) / 2.
Proof. Time radcan. Qed.

Lemma c7 : 10.-root (-1 : C) ^+ 2 + (5.-root (-1))^-1 = (2.-root 5 + 1) / 2.
Proof. Time radcan. Qed.

(* the goals of the former sqrt 2, 3, 5 table (Tutorial 33) *)
Lemma c8 : 2 * 5.-root (-1 : C) - 2 * 5.-root (-1) ^+ 4 - 1 = 2.-root 5.
Proof. Time radcan. Qed.

Lemma c9 : 8.-root (-1 : C) ^+ 2 + (8.-root (-1)) ^- 2 = 2.-root 2.
Proof. Time radcan. Qed.

(* sqrt 11 (= 3 mod 4) with omega_22 *)
Lemma c10 : 2.-root (11 : C) * 22.-root (-1) ^+ 11 =
  \sum_(a < 11) 22.-root (-1 : C) ^+ ((11 * 3 + a * a * 4 + 11) %% 44).
Proof. rewrite !big_ord_recr big_ord0 /=. Time radcan. Qed.

(* false identities are refused *)
Goal 2.-root (7 : C) = 14.-root (-1) ^+ 21 + 2 * 14.-root (-1) ^+ 25
  + 2 * 14.-root (-1) ^+ 9 + 14.-root (-1).
Proof. Fail radcan. Abort.

Goal 5.-root (-1 : C) ^+ 2 + (5.-root (-1)) ^- 2 = (2.-root 5 + 1) / 2.
Proof. Fail radcan. Abort.

(* limitations: omega_7 ^+ 7 = -1, but sqrt 7 is substituted only with *)
(* the omega_14 of the goal: here the sums are compared after reduction   *)
Goal 2.-root (7 : C) * 7.-root (-1) ^+ 7 =
  - (14.-root (-1) ^+ 21 + 2 * 14.-root (-1) ^+ 25
     + 2 * 14.-root (-1) ^+ 9 + 2 * 14.-root (-1)).
Proof. Time radcan. Qed.

(* inverses: of a sum of omegas (Tutorial 36), of a sum of radicals     *)
(* (rationalised by the normaliser), then the substitution               *)
Goal (5.-root (-1 : C) ^+ 2 + (5.-root (-1)) ^- 2)^-1 = 2 / (2.-root 5 - 1).
Proof. Time radcan. Qed.
End Complex.
