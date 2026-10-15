(******************************************************************************)
(* Tutorial 23: irreducible factors of the radicands (M16, form 1 of the      *)
(* paper).  The basis of the radicands is coprime and square-free (form 2,    *)
(* Tutorial 14), and that basis is already canonical: sqrt (x^2 - 1) and      *)
(* sqrt (x - 1) * sqrt (x + 1) meet as soon as both appear in the goal.       *)
(* Splitting a radicand into irreducible factors over Z (IrrFactor, MFactor,  *)
(* MFactorEEZ) asks stronger conditions (0 <= x - 1 and 0 <= x + 1 instead    *)
(* of 0 <= x ^+ 2 - 1), so radcan tries the irreducible basis last, only      *)
(* when every other attempt fails.  Every factorisation is checked by         *)
(* multiplication.                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Refine.
From Radcan Require Import Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* raw: 0 <= x + 1, 0 <= x - 1   refined: 1 <= x *)
Lemma f1 : 1 <= x -> \sqrt (x ^+ 2 - 1) = \sqrt (x - 1) * \sqrt (x + 1).
Proof. move=> h. radcan. Show. exact: h. Qed.

(* x^4 - 1 = (x^2 - 1)(x^2 + 1): refined 1 <= x ^+ 2 *)
Lemma f2 : 1 <= x ^+ 2 ->
  \sqrt (x ^+ 4 - 1) / \sqrt (x ^+ 2 + 1) = \sqrt (x ^+ 2 - 1).
Proof. move=> h. radcan. Show. exact: h. Qed.

(* two variables: x^2 - y^2 = (x - y)(x + y) *)
Lemma f3 : y <= x -> 0 <= x + y ->
  \sqrt (x ^+ 2 - y ^+ 2) = \sqrt (x - y) * \sqrt (x + y).
Proof. move=> h1 h2. radcan. Show. all: by []. Qed.

(* x^3 - y^3 = (x - y)(x^2 + x y + y^2) *)
Lemma f4 : y < x -> 0 <= x * y + x ^+ 2 + y ^+ 2 ->
  \sqrt (x ^+ 3 - y ^+ 3) / \sqrt (x - y) = \sqrt (x ^+ 2 + x * y + y ^+ 2).
Proof. move=> h1 h2. radcan. Show. all: by []. Qed.

(* x y + x + y + 1 = (x + 1)(y + 1) *)
Lemma f5 : -1 <= x -> -1 <= y ->
  \sqrt (x * y + x + y + 1) = \sqrt (x + 1) * \sqrt (y + 1).
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* the paper's form 1: (x + 3)^2 (x + 1)(x + 2), refined -1 <= x *)
Lemma f6 : -1 <= x ->
  \sqrt (x ^+ 4 + 9 * x ^+ 3 + 29 * x ^+ 2 + 39 * x + 18) =
  (x + 3) * \sqrt (x + 1) * \sqrt (x + 2).
Proof. move=> h. radcan. Show. exact: h. Qed.

(* no factor of degree 1 in any variable (Wang's EEZ in MFactorEEZ) *)
(* refined: -1 <= 210 * x ^+ 2 + y ^+ 3, -11 <= x ^+ 2 + 2 * y ^+ 2 *)
Lemma f7 : -1 <= 210 * x ^+ 2 + y ^+ 3 -> -11 <= x ^+ 2 + 2 * y ^+ 2 ->
  \sqrt (210 * x ^+ 4 + 420 * x ^+ 2 * y ^+ 2 + 2311 * x ^+ 2 +
         x ^+ 2 * y ^+ 3 + 2 * y ^+ 5 + 11 * y ^+ 3 + 2 * y ^+ 2 + 11) =
  \sqrt (210 * x ^+ 2 + y ^+ 3 + 1) * \sqrt (x ^+ 2 + 2 * y ^+ 2 + 11).
Proof. move=> h1 h2. radcan. Show. all: by []. Qed.
End Generic.

(* the normal form itself: form 2 keeps sqrt (x^2 + 3x + 2), the           *)
(* irreducible basis (form 1) gives sqrt (x + 1) * sqrt (x + 2)              *)
Definition P1 : rexpr :=
  RAdd (RAdd (RAdd (RAdd (RPow (RVar 0) 4) (RMul (RCst 9) (RPow (RVar 0) 3)))
                   (RMul (RCst 29) (RPow (RVar 0) 2)))
             (RMul (RCst 39) (RVar 0))) (RCst 18).
Definition sqP1 := RRootE 2 P1.
Compute nf_to_rexpr (radcan_nf MStd sqP1 sqP1).1.1.
Compute
  let hs := neg_hints [:: sqP1] in
  let bs := irr_basis (mk_basis_n false MStd hs [:: sqP1]) in
  nf_to_rexpr (radcan_nfb false MStd hs bs sqP1 sqP1).1.1.

(* on Stdlib reals the refined conditions are closed by lra *)
Local Open Scope R_scope.
Lemma sf1 (x : R) : 1 <= x -> sqrt (x ^ 2 - 1) = sqrt (x - 1) * sqrt (x + 1).
Proof. move=> h. radcan_Rstd. radcan. all: radcan_Rstd_back; lra. Qed.

Lemma sf2 (x y : R) : y <= x -> 0 <= x + y ->
  sqrt (x ^ 2 - y ^ 2) = sqrt (x - y) * sqrt (x + y).
Proof. move=> h1 h2. radcan_Rstd. radcan. all: radcan_Rstd_back; lra. Qed.
