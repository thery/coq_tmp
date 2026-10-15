(******************************************************************************)
(* GcdTests: the fast polynomial gcd (MGcd.mgcd, used by Poly.pgcd):          *)
(* square roots of 3-variable radicands, gcds of 3- and 4-variable products   *)
(* sharing a factor, and timings of the new pgcd against the old primitive    *)
(* pseudo-remainder sequence pgcd_prs.  Timings (vm_compute, Rocq 9.1.1) in   *)
(* comments; old pgcd on the 3-variable radicand: > 200 s (M16 report).       *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan.

Definition X := RVar 0.
Definition Y := RVar 1.
Definition Z' := RVar 2.
Definition W := RVar 3.
Definition one := RCst Z1.
Definition cst z := RCst z.
Definition pw e k := RPow e k.
Definition sq e := RRootE 2 e.

(* gcd checked against the expected factor *)
Definition gcd_is (a b g : rexpr) : bool :=
  nf_eqb (pgcd gcd_fuel (pnorm a) (pnorm b)) (pnormal (pnorm g)).

(* The 3-variable radicand of the M16 report:                             *)
(* P = (x y + y z + z^2 + 1)(x^3 + y^2 z + x z - 5), expanded              *)
Definition f1 := RAdd (RAdd (RMul X Y) (RMul Y Z')) (RAdd (pw Z' 2) one).
Definition f2 :=
  RAdd (RAdd (pw X 3) (RMul (pw Y 2) Z')) (RAdd (RMul X Z') (cst (-5))).
Definition P := Eval vm_compute in nf_to_rexpr (pnorm (RMul f1 f2)).

(* 0.05 s *)
Time Eval vm_compute in size (mk_basis [:: sq P]).

(* sqrt P = sqrt f1 * sqrt f2 when 0 <= f1 and 0 <= f2, 0.07 s *)
Example sqrtP :
  radcan_check (sq P) (RMul (sq f1) (sq f2)) =
  Some [:: CGe0 (RAdd (RMul (pw Y 2) Z')
                      (RAdd (pw X 3) (RAdd (RMul X Z') (cst (-5)))));
           CGe0 (RAdd (pw Z' 2)
                      (RAdd (RMul Y Z') (RAdd (RMul X Y) one)))].
Proof. by vm_compute. Qed.

(* sqrt (P f1) = f1 sqrt f2 when 0 <= f1 and 0 <= f2 *)
Time Eval vm_compute in radcan_check (sq (RMul P f1)) (RMul f1 (sq f2)).

(* gcd (P, dP/dx) = 1 (pre-test), gcd (P, f1 (x + 7)) = f1 *)
Definition dPx := RAdd (RMul Y f2) (RMul f1 (RAdd (RMul (cst 3) (pw X 2)) Z')).
Example gcd3_1 : gcd_is P dPx one.
Proof. by vm_compute. Qed.
Example gcd3_2 : gcd_is P (RMul f1 (RAdd X (cst 7))) f1.
Proof. by vm_compute. Qed.

(* gcd (f1^2 f2, f1 f2^3) = f1 f2, 0.05 s *)
Example gcd3_3 : gcd_is (RMul (pw f1 2) f2) (RMul f1 (pw f2 3)) (RMul f1 f2).
Proof. by vm_compute. Qed.

(* 3 variables, total degree 8 *)
Definition f3 :=
  RAdd (RMul (pw X 2) (pw Z' 2))
       (RSub (RMul (cst 3) (pw Y 3)) (RMul X (cst 4))).
Example gcd3_4 : gcd_is (RMul f1 (RMul f2 f2)) (RMul f2 f3) f2.
Proof. by vm_compute. Qed.

(* 4 variables *)
Definition g1 := RAdd (RMul X W) (RAdd (RMul Y Z') one).
Definition g2 := RAdd (pw X 2) (RSub (RMul Y W) (pw Z' 2)).
Definition g3 := RSub (RMul (pw W 2) Y) (RAdd X (cst 3)).
Example gcd4_1 : gcd_is (RMul g1 g2) (RMul g1 g3) g1.
Proof. by vm_compute. Qed.
Example gcd4_2 :
  gcd_is (RMul g1 (RMul g2 g3)) (RMul (pw g2 2) g3) (RMul g2 g3).
Proof. by vm_compute. Qed.

(* total degrees 8 and 9, degree up to 6 in one variable: 0.6 s *)
Definition h1 :=
  RAdd (RMul (cst 12) (RMul (pw X 2) (pw Y 3)))
       (RAdd (RMul (cst (-7)) (RMul Z' (pw W 2)))
             (RAdd (RMul X (RMul Y (RMul Z' W))) (cst 11))).
Definition h2 := RSub (pw (RAdd X (RAdd Y (RAdd Z' W))) 3) (cst 2).
Definition h3 :=
  RAdd (RMul (cst 5) (pw W 4)) (RSub (RMul X Z') (RMul (cst 3) Y)).
Example gcd4_3 :
  gcd_is (RMul (cst 6) (RMul h1 h2)) (RMul (cst 4) (RMul h1 h3)) h1.
Proof. by vm_compute. Qed.
Example gcd4_4 : gcd_is (RMul h1 g2) (RMul h1 g3) h1.
Proof. by vm_compute. Qed.

Time Eval vm_compute in gcd_is (RMul P f1) (RMul f1 f3) f1.
Time Eval vm_compute in gcd_is (RMul g1 (RMul g2 g3)) (RMul (pw g2 2) g3)
                               (RMul g2 g3).
Time Eval vm_compute in
  gcd_is (RMul (cst 6) (RMul h1 h2)) (RMul (cst 4) (RMul h1 h3)) h1.

(* Old against new on small inputs (no regression): same result, times *)
(* of the old pgcd_prs and of the new pgcd                             *)
Definition G1 := RAdd (RAdd (RMul (cst 210) (pw X 2)) (pw Y 3)) one.
Definition G2 := RAdd (RAdd (pw X 2) (RMul (cst 2) (pw Y 2))) (cst 11).
Definition small : seq (rexpr * rexpr) :=
  [:: (RSub (pw X 2) one, RAdd (RAdd (pw X 2) (RMul (cst 2) X)) one);
      (RSub (pw X 2) (pw Y 2), RAdd (RAdd (pw X 2) (RMul (cst 2) (RMul X Y)))
                                    (pw Y 2));
      (RMul G1 G2, RMul G1 (RAdd X Y));
      (RMul (pw G1 2) G2, RMul G1 (pw G2 2));
      (RMul f1 (RAdd X one), RMul f1 (RSub Y one))].

(* pgcd_prs is only used in Eval commands: a definition using it would    *)
(* need the native code of Radcan, see tutorial/check.sh                  *)
(* = true: the same results *)
Eval vm_compute in
  all (fun ab => nf_eqb (pgcd gcd_fuel (pnorm ab.1) (pnorm ab.2))
                        (pgcd_prs gcd_fuel (pnorm ab.1) (pnorm ab.2))) small.

(* old 0.015 s, new 0.08 s: conversion and pre-test overhead on tiny inputs *)
Time Eval vm_compute in
  map (fun ab => size (pgcd_prs gcd_fuel (pnorm ab.1) (pnorm ab.2))) small.
Time Eval vm_compute in
  map (fun ab => size (pgcd gcd_fuel (pnorm ab.1) (pnorm ab.2))) small.
