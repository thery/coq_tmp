From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootR Syntax Radcan Refine OddRoot Tactic RootRstd RadcanBig.

Local Open Scope R_scope.
(* big Stdlib numerals: binary all the way, factoring by small primes + gcd basis *)
Lemma b1 : sqrt (1000000007 ^ 2 * 3) = 1000000007 * sqrt 3.
Proof. radcan_Rstd. radcan. Qed.

Lemma b2 : sqrt (1000003 * 1000033) * sqrt 1000003 = 1000003 * sqrt 1000033.
Proof. radcan_Rstd. radcan. Qed.

Lemma b3 : sqrt 1000000007 * sqrt 1000000007 = 1000000007.
Proof. radcan_Rstd. radcan. Qed.

(* the same with the BigZ/BigQ backend *)
Lemma b4 : sqrt (1000003 * 1000033) * sqrt 1000003 = 1000003 * sqrt 1000033.
Proof. radcan_Rstd. radcan_big. Qed.

Lemma b5 : / (sqrt 2 + sqrt 3 + sqrt 5) * (sqrt 2 + sqrt 3 + sqrt 5) = 1.
Proof. radcan_Rstd. radcan_big. Qed.
