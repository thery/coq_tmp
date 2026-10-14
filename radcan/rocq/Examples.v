(******************************************************************************)
(* Examples: tests and timings of the normaliser (Radcan.v), by feature:      *)
(* constants, variables, division, variables under roots with side            *)
(* conditions, large radicands, several indices, negative radicands (odd      *)
(* mode), polynomial gcd, roots of -1 (neg mode), inverse atoms.              *)
(*   nrm e == the normal form of e and its side conditions                    *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Radcan.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Constants *)
Definition nrm (e : rexpr) := normc MStd [::] (mk_basis [:: e]) e.
Definition sqrt_ (p : positive) := RRoot (xO xH) p.

Time Eval vm_compute in nrm (RMul (sqrt_ 2%positive) (sqrt_ 3%positive)).
Time Eval vm_compute in nrm (RPow (RAdd (RCst Z1) (sqrt_ 2%positive)) 2).
Time Eval vm_compute in nrm (sqrt_ 8%positive).
Time Eval vm_compute in
  nrm (RMul (RRoot 3%positive 2%positive) (sqrt_ 2%positive)).
Time Eval vm_compute in nrm (RSub (sqrt_ 12%positive) (sqrt_ 3%positive)).
Time Eval vm_compute in
  nrm (RPow (RAdd (RRoot 3%positive 2%positive)
                  (RAdd (sqrt_ 3%positive) (RRoot 5%positive 7%positive)))
            10).
Time Eval vm_compute in nrm (RRoot 2%positive 1000000007%positive).

Example ex_sqrt6 : radcan_check ( (RMul (sqrt_ 2%positive) (sqrt_ 3%positive)))
                          ((sqrt_ 6%positive)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_sq : radcan_check ( (RPow (RAdd (RCst Z1) (sqrt_ 2%positive)) 2))
  ((RAdd (RCst (Zpos 3)) (RMul (RCst (Zpos 2)) (sqrt_ 2%positive)))) =
  Some [::].
Proof. by vm_compute. Qed.

Example ex_sqrt8 : radcan_check ( (sqrt_ 8%positive))
  ((RMul (RCst (Zpos 2)) (sqrt_ 2%positive))) = Some [::].
Proof. by vm_compute. Qed.

Example ex_cbrt :
  radcan_check ( (RMul (RRoot 3%positive 2%positive) (sqrt_ 2%positive)))
  ((RRoot 6%positive 32%positive)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_sqrt12 :
  radcan_check ( (RSub (sqrt_ 12%positive) (sqrt_ 3%positive)))
  ((sqrt_ 3%positive)) = Some [::].
Proof. by vm_compute. Qed.

(* In a field *)
Local Open Scope ring_scope.

Example ex_field (F : numFieldType) (r : posroot F) :
  proot r 3 2 * proot r 2 2 = proot r 6 32.
Proof.
apply: (@radcan_eq F r [::] (RMul (RRoot 3 2) (RRoot 2 2)) (RRoot 6 32)).
by vm_compute.
Qed.

Example ex_field2 (F : numFieldType) (r : posroot F) :
  (1 + proot r 2 2) ^+ 2 = 3 + 2 * proot r 2 2.
Proof.
apply: (@radcan_eq F r [::] (RPow (RAdd (RCst Z1) (RRoot 2 2)) 2)
           (RAdd (RCst (Zpos 3)) (RMul (RCst (Zpos 2)) (RRoot 2 2)))).
by vm_compute.
Qed.

(* Variables outside roots *)
Definition X := RVar 0.
Definition Y := RVar 1.
Definition two := RCst (Zpos 2).
Definition three := RCst (Zpos 3).

Example ex_var1 : radcan_check ( (RMul X (sqrt_ 2%positive)))
                         ((RMul (sqrt_ 2%positive) X)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_var2 :
  radcan_check ( (RAdd (RMul X (sqrt_ 2%positive)) (RMul X (sqrt_ 2%positive))))
         ((RMul (RMul two X) (sqrt_ 2%positive))) = Some [::].
Proof. by vm_compute. Qed.

Example ex_var3 :
  radcan_check ( (RPow (RAdd X (sqrt_ 2%positive)) 2))
         ((RAdd (RAdd (RPow X 2) (RMul (RMul two X) (sqrt_ 2%positive))) two))
  = Some [::].
Proof. by vm_compute. Qed.

Example ex_var4 :
  radcan_check ( (RMul (RSub X (RMul Y (sqrt_ 3%positive)))
                     (RAdd X (RMul Y (sqrt_ 3%positive)))))
         ((RSub (RPow X 2) (RMul three (RPow Y 2)))) = Some [::].
Proof. by vm_compute. Qed.

Definition cbrt_ (p : positive) := RRoot 3%positive p.

Example ex_var5 :
  radcan_check ( (RPow (RAdd X (cbrt_ 2%positive)) 3))
         ((RAdd (RAdd (RAdd (RPow X 3)
                                 (RMul (RMul three (RPow X 2))
                                       (cbrt_ 2%positive)))
                           (RMul (RMul three X) (cbrt_ 4%positive)))
                     two)) = Some [::].
Proof. by vm_compute. Qed.

Time Eval vm_compute in nrm (RPow (RAdd X (cbrt_ 2%positive)) 3).
Time Eval vm_compute in
  nrm (RPow (RAdd (RAdd X (cbrt_ 2%positive)) (RAdd Y (sqrt_ 3%positive))) 12).

Example ex_field_var (F : numFieldType) (r : posroot F) (x y : F) :
  (x - y * proot r 2 3) * (x + y * proot r 2 3) = x ^+ 2 - 3 * y ^+ 2.
Proof.
apply: (@radcan_eq F r [:: x; y]
         (RMul (RSub (RVar 0) (RMul (RVar 1) (RRoot 2 3)))
               (RAdd (RVar 0) (RMul (RVar 1) (RRoot 2 3))))
         (RSub (RPow (RVar 0) 2) (RMul (RCst (Zpos 3)) (RPow (RVar 1) 2)))).
by vm_compute.
Qed.

Example ex_field_var2 (F : numFieldType) (r : posroot F) (x : F) :
  (x + proot r 3 2) ^+ 3 = x ^+ 3 + 3 * x ^+ 2 * proot r 3 2
                           + 3 * x * proot r 3 4 + 2.
Proof.
apply: (@radcan_eq F r [:: x]
         (RPow (RAdd (RVar 0) (RRoot 3 2)) 3)
         (RAdd (RAdd (RAdd (RPow (RVar 0) 3)
                           (RMul (RMul (RCst (Zpos 3)) (RPow (RVar 0) 2))
                                 (RRoot 3 2)))
                     (RMul (RMul (RCst (Zpos 3)) (RVar 0)) (RRoot 3 4)))
               (RCst (Zpos 2)))).
by vm_compute.
Qed.

(* Division *)

Example ex_div1 : radcan_check ( (RInv (sqrt_ 2%positive)))
  ((RMul (sqrt_ 2%positive) (RInv two))) = Some [::].
Proof. by vm_compute. Qed.

Example ex_div2 : radcan_check ( (RInv (RAdd (RCst Z1) (sqrt_ 2%positive))))
  ((RSub (sqrt_ 2%positive) (RCst Z1))) = Some [::].
Proof. by vm_compute. Qed.

Example ex_div3 :
  radcan_check ( (RMul (RAdd (sqrt_ 3%positive) (sqrt_ 2%positive))
                     (RInv (RSub (sqrt_ 3%positive) (sqrt_ 2%positive)))))
         ((RAdd (RCst (Zpos 5)) (RMul two (sqrt_ 6%positive)))) = Some [::].
Proof. by vm_compute. Qed.

Example ex_div4 : radcan_check ( (RInv (cbrt_ 2%positive)))
  ((RMul (cbrt_ 4%positive) (RInv two))) = Some [::].
Proof. by vm_compute. Qed.

Example ex_div5 :
  radcan_check ( (RAdd (RMul X (RInv (sqrt_ 2%positive)))
                     (RMul X (RInv (sqrt_ 2%positive)))))
         ((RMul X (sqrt_ 2%positive))) = Some [::].
Proof. by vm_compute. Qed.

Example ex_div6 :
  radcan_check
    ( (RInv (RAdd (RAdd (RCst Z1) (sqrt_ 2%positive)) (sqrt_ 3%positive))))
         ((RMul (RSub (RAdd two (sqrt_ 2%positive)) (sqrt_ 6%positive))
                     (RInv (RCst (Zpos 4))))) = Some [::].
Proof. by vm_compute. Qed.

Example ex_div7 :
  radcan_check ( (RMul (RAdd X (sqrt_ 2%positive)) (RInv three)))
         ((RAdd (RMul X (RInv three)) (RMul (sqrt_ 2%positive) (RInv three))))
  = Some [::].
Proof. by vm_compute. Qed.

(* inverses that cannot be computed become atoms; cancelling records x+1 != 0 *)
Example ex_div_atom :
  radcan_check
    ( (RAdd (RMul X (RInv (RAdd X (RCst Z1)))) (RInv (RAdd (RCst Z1) X))))
         ((RMul (RAdd (RCst Z1) X) (RInv (RAdd X (RCst Z1))))) =
  Some [:: CNeq0 (RAdd X (RCst Z1))].
Proof. by vm_compute. Qed.

Time Eval vm_compute in
  nrm (RInv (RAdd (RAdd (RCst Z1) (sqrt_ 2%positive)) (sqrt_ 3%positive))).
Time Eval vm_compute in
  nrm (RInv (RAdd (RAdd (RRoot 3%positive 2%positive) (sqrt_ 3%positive))
                   (RRoot 5%positive 7%positive))).
Time Eval vm_compute in
  nrm (RInv (RAdd (RAdd (sqrt_ 2%positive) (sqrt_ 3%positive))
                   (RAdd (sqrt_ 5%positive) (sqrt_ 7%positive)))).

Example ex_field_div (F : numFieldType) (r : posroot F) :
  1 / (1 + proot r 2 2 + proot r 2 3) = (2 + proot r 2 2 - proot r 2 6) / 4.
Proof.
apply: (@radcan_eq F r [::]
  (RMul (RCst Z1) (RInv (RAdd (RAdd (RCst Z1) (RRoot 2 2)) (RRoot 2 3))))
  (RMul (RSub (RAdd (RCst (Zpos 2)) (RRoot 2 2)) (RRoot 2 6))
        (RInv (RCst (Zpos 4))))).
by vm_compute.
Qed.

Example ex_field_div2 (F : numFieldType) (r : posroot F) (x : F) :
  x / proot r 2 2 + x / proot r 2 2 = x * proot r 2 2.
Proof.
apply: (@radcan_eq F r [:: x]
  (RAdd (RMul (RVar 0) (RInv (RRoot 2 2))) (RMul (RVar 0) (RInv (RRoot 2 2))))
  (RMul (RVar 0) (RRoot 2 2))).
by vm_compute.
Qed.

(* Variables under roots, rational functions; side conditions *)
Definition sq (e : rexpr) := RRootE 2%positive e.
Definition cb (e : rexpr) := RRootE 3%positive e.
Definition one := RCst Z1.
Definition four := RCst (Zpos 4).

Example ex_rat1 : radcan_check (sq (RPow X 2)) X = Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_rat2 :
  radcan_check (sq (RMul four X)) (RMul two (sq X)) = Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_rat3 : radcan_check (RMul (sq X) (sq X)) X = Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_r4 :
  radcan_check (sq (RPow X 3)) (RMul X (sq X)) = Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_r5 :
  radcan_check (RMul (cb X) (cb (RPow X 2))) X = Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_r6 : radcan_check (sq (RMul X Y)) (RMul (sq X) (sq Y)) =
  Some [:: CGe0 X; CGe0 Y].
Proof. by vm_compute. Qed.

Definition xm1 := RAdd X (RCst (Zneg 1)).
Definition xp1 := RAdd X one.

Example ex_r7 :
  radcan_check (sq (RSub (RPow X 2) one))
               (RMul (sq (RSub X one)) (sq (RAdd X one))) =
  Some [:: CGe0 xp1; CGe0 xm1].
Proof. by vm_compute. Qed.

(* sqrt (x^2 - 1) / sqrt (x - 1) = sqrt (x + 1) *)
Example ex_r8 :
  radcan_check (RMul (sq (RSub (RPow X 2) one)) (RInv (sq (RSub X one))))
               (sq (RAdd X one)) =
  Some [:: CGe0 xp1; CGe0 xm1; CNeq0 xm1].
Proof. by vm_compute. Qed.

Example ex_q1 :
  radcan_check (RMul (RSub (RPow X 2) one) (RInv (RSub X one))) (RAdd X one) =
  Some [:: CNeq0 xm1].
Proof. by vm_compute. Qed.

Example ex_q2 :
  radcan_check (RMul (RMul (RSub (RPow X 2) one) (RInv (RAdd X one)))
                     (RInv (RSub X one)))
               one = Some [:: CNeq0 xp1; CNeq0 xm1].
Proof. by vm_compute. Qed.

Example ex_q3 : radcan_check (RMul X (RInv X)) one = Some [:: CNeq0 X].
Proof. by vm_compute. Qed.

Example ex_q4 :
  radcan_check (RMul (RAdd (RMul X Y) X) (RInv X)) (RAdd Y one) =
  Some [:: CNeq0 X].
Proof. by vm_compute. Qed.

Time Eval vm_compute in
  radcan_check (RMul (sq (RSub (RPow X 2) one)) (RInv (sq (RSub X one))))
               (sq (RAdd X one)).

(* in a field: the conditions become hypotheses *)
Example ex_field_r (F : numFieldType) (r : posroot F) (x : F) :
  0 <= x + 1 -> 0 <= x - 1 -> x - 1 != 0 ->
  proot r 2 (x ^+ 2 - 1) / proot r 2 (x - 1) = proot r 2 (x + 1).
Proof.
move=> h1 h2 h3.
have := @radcan_eq_cond F r [:: x]
  (RMul (RRootE 2 (RSub (RPow (RVar 0) 2) (RCst Z1)))
        (RInv (RRootE 2 (RSub (RVar 0) (RCst Z1)))))
  (RRootE 2 (RAdd (RVar 0) (RCst Z1))) [:: CGe0 xp1; CGe0 xm1; CNeq0 xm1].
apply; first by vm_compute.
by split; [exact: h1 | split; [exact: h2 | exact: h3]].
Qed.

(* root-free goals in a numFieldType without roots *)
Example ex_field_q0 (F : numFieldType) (x : F) : x != 0 -> x / x = 1.
Proof.
move=> hx.
have := @radcan_eq_cond0 F [:: x] (RMul (RVar 0) (RInv (RVar 0))) (RCst Z1)
          [:: CNeq0 (RVar 0)] erefl erefl.
by apply; first by vm_compute.
Qed.

Example ex_field_q1 (F : numFieldType) (x : F) : x - 1 != 0 ->
  (x ^+ 2 - 1) / (x - 1) = x + 1.
Proof.
move=> hx.
have := @radcan_eq_cond0 F [:: x]
  (RMul (RSub (RPow (RVar 0) 2) (RCst Z1)) (RInv (RSub (RVar 0) (RCst Z1))))
  (RAdd (RVar 0) (RCst Z1)) [:: CNeq0 xm1] erefl erefl.
by apply; first by vm_compute.
Qed.

(* Large constant radicands: trial division by primes < 1000, perfect
   powers, coprime basis of the radicands of the goal *)
Example ex_big1 : radcan_check (RRoot 2 (1000000007 * 1000000007 * 3))
                               (RMul (RCst 1000000007) (RRoot 2 3)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_big2 :
  radcan_check (RMul (RRoot 2 (1000003 * 1000033)) (RRoot 2 1000003))
               (RMul (RCst 1000003) (RRoot 2 1000033)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_big3 :
  radcan_check (RMul (sq (RMul (RCst 1000003) (RCst 1000033)))
                     (sq (RCst 1000003)))
               (RMul (RCst 1000003) (RRoot 2 1000033)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_big4 :
  radcan_check (RMul (sqrt_ 6) (sqrt_ 15)) (RMul three (sqrt_ 10)) = Some [::].
Proof. by vm_compute. Qed.

Time Eval vm_compute in radcan_check (RRoot 2 1000000007) (RRoot 2 1000000007).

(* The same base under different root indices *)
Definition xm1' := RSub X one.

Example ex_i1 : radcan_check (RMul (sq X) (cb X)) (RRootE 6 (RPow X 5)) =
  Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_i2 : radcan_check (RMul (sq X) (RInv (cb X))) (RRootE 6 X) =
  Some [:: CGe0 X; CNeq0 X].
Proof. by vm_compute. Qed.

Example ex_i3 : radcan_check (RPow (RRootE 4 X) 2) (sq X) = Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_i4 : radcan_check (RRootE 6 (RPow X 3)) (sq X) = Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_i5 :
  radcan_check (RMul (sq xm1') (cb xm1')) (RRootE 6 (RPow xm1' 5)) =
  Some [:: CGe0 xm1].
Proof. by vm_compute. Qed.

(* different bases are not merged; constant radicands need no condition *)
Example ex_i6 :
  radcan_check (RMul (sqrt_ 2) (cb X)) (RMul (cb X) (sqrt_ 2)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_i7 :
  radcan_check (RMul (sqrt_ 2) (cb X)) (RRootE 6 (RMul (RCst 8) (RPow X 2))) =
  Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_i8 :
  radcan_check (RMul (RMul (sq X) (RRootE 4 X)) (RRootE 8 X))
               (RRootE 8 (RPow X 7)) =
  Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_i9 :
  radcan_check (RMul (sq (RMul X Y)) (cb X))
               (RMul (RRootE 6 (RPow X 5)) (sq Y)) =
  Some [:: CGe0 Y; CGe0 X].
Proof. by vm_compute. Qed.

Time Eval vm_compute in
  radcan_check (RPow (RAdd (sq X) (cb X)) 6) (RPow (RAdd (cb X) (sq X)) 6).

(* Negative radicands.  Main checker: an even root of B keeps the base B
   (condition 0 <= B), negative constants under roots stay atoms.  Odd mode
   (radcan_check_odd): proot n (- a) = - proot n a for odd n *)
Definition neg (p : positive) := ROpp (RCst (Zpos p)).
Definition omx := RSub one X.
(* how 1 - x is printed in the conditions *)
Definition omx' := RAdd (RMul (RCst (Zneg 1)) X) one.

(* the cube root of -8 is -2: odd mode only *)
Example ex_n1 : radcan_check_odd (cb (neg 8)) (neg 2) = Some [::].
Proof. by vm_compute. Qed.

(* not accepted for a generic posroot (false on C with n.-root) *)
Example ex_n1_main : radcan_check (cb (neg 8)) (neg 2) = None.
Proof. by vm_compute. Qed.

Example ex_n2 :
  radcan_check_odd (RMul (cb (neg 2)) (cb (neg 4))) two = Some [::].
Proof. by vm_compute. Qed.

Example ex_n3 :
  radcan_check_odd (RMul (cb (neg 2)) (cb four)) (neg 2) = Some [::].
Proof. by vm_compute. Qed.

Example ex_n4 : radcan_check_odd (RPow (cb (neg 3)) 3) (neg 3) = Some [::].
Proof. by vm_compute. Qed.

Example ex_n5 :
  radcan_check_odd (RAdd (RRootE 5 (neg 32)) two) (RCst 0) = Some [::].
Proof. by vm_compute. Qed.

Example ex_n6 : radcan_check_odd (RInv (cb (neg 2)))
  (RMul (neg 1) (RMul (cb four) (RInv two))) = Some [::].
Proof. by vm_compute. Qed.

(* even roots of negative constants are never simplified *)
Example ex_n7 : radcan_check_odd (sq (neg 4)) two = None.
Proof. by vm_compute. Qed.

(* polynomial radicands: cbrt (1 - x) = - cbrt (x - 1), no condition *)
Example ex_n8 : radcan_check_odd (cb omx) (ROpp (cb xm1')) = Some [::].
Proof. by vm_compute. Qed.

Example ex_n9 : radcan_check_odd (RMul (cb omx) (RPow (cb xm1') 2)) omx =
  Some [:: CGe0 xm1].
Proof. by vm_compute. Qed.

Example ex_n10 :
  radcan_check_odd (cb (RMul (neg 8) (RPow X 3))) (RMul (neg 2) X) =
  Some [:: CGe0 X].
Proof. by vm_compute. Qed.

Example ex_n11 :
  radcan_check_odd (cb (RSub one (RPow X 2)))
                   (ROpp (RMul (cb xm1') (cb (RAdd X one)))) =
  Some [:: CGe0 xp1; CGe0 xm1].
Proof. by vm_compute. Qed.

(* even roots, main checker: the base keeps the sign of the radicand *)
Example ex_n12 : radcan_check (RPow (sq omx) 2) omx = Some [:: CGe0 omx'].
Proof. by vm_compute. Qed.

Example ex_n13 :
  radcan_check (RMul (sq omx) (sq omx)) omx = Some [:: CGe0 omx'].
Proof. by vm_compute. Qed.

(* x - 1 is in the basis, sqrt (1 - x) still has base 1 - x *)
Example ex_n14 :
  radcan_check (RAdd (RMul (sq xm1') (sq xm1')) (RMul (sq omx) (sq omx)))
               (RCst 0) =
  Some [:: CGe0 xm1; CGe0 omx'].
Proof. by vm_compute. Qed.

Example ex_n15 :
  radcan_check (RMul (sq (RSub one (RPow X 2))) (RInv (sq omx)))
               (sq (RAdd X one)) =
  Some [:: CGe0 xp1; CGe0 omx'; CNeq0 omx'].
Proof. by vm_compute. Qed.

(* sqrt (1 - x) * sqrt (x - 1) = 0 (x = 1) is not proved: distinct atoms *)
Example ex_n16 : radcan_check (RMul (sq omx) (sq xm1')) (RCst 0) = None.
Proof. by vm_compute. Qed.

Time Eval vm_compute in
  radcan_check_odd (RAdd (RRootE 5 (neg 32)) two) (RCst 0).
Time Eval vm_compute in
  radcan_check_odd (cb (RSub one (RPow X 2)))
                   (ROpp (RMul (cb xm1') (cb (RAdd X one)))).
Time Eval vm_compute in
  radcan_check (RMul (sq (RSub one (RPow X 2))) (RInv (sq omx)))
               (sq (RAdd X one)).

(* in a field with real odd roots *)
Example ex_field_n1 (F : numFieldType) (r : posroot F) (o : oddroot r) :
  proot r 3 (- 8) = - 2.
Proof.
by apply: (@radcan_eq_odd F r o [::] (cb (neg 8)) (neg 2)); vm_compute.
Qed.

Example ex_field_n2 (F : numFieldType) (r : posroot F) (o : oddroot r) (x : F) :
  0 <= x - 1 -> proot r 3 (1 - x) * proot r 3 (x - 1) ^+ 2 = 1 - x.
Proof.
move=> h.
apply: (@radcan_eq_cond_odd F r o [:: x] (RMul (cb omx) (RPow (cb xm1') 2)) omx
          [:: CGe0 xm1]); first by vm_compute.
exact: h.
Qed.

(* Polynomial gcd and square-free decomposition of the radicands (Poly.v) *)
(* (x+1)^2 *)
Definition x2p2xp1 := RAdd (RAdd (RPow X 2) (RMul two X)) one.
(* (x-1)^3 *)
Definition xm1_3 :=
  RAdd (RSub (RAdd (RPow X 3) (RMul three X)) (RMul three (RPow X 2)))
       (RCst (Zneg 1)).
(* (x^2-1)^2 *)
Definition x4m2x2p1 := RAdd (RSub (RPow X 4) (RMul two (RPow X 2))) one.
Definition x2m1 := RAdd (RPow X 2) (RCst (Zneg 1)).
(* (x+y)^2 *)
Definition xy2 := RAdd (RAdd (RPow X 2) (RMul (RMul two X) Y)) (RPow Y 2).
Definition yx := RAdd Y X.

Example ex_g1 : radcan_check (sq x2p2xp1) xp1 = Some [:: CGe0 xp1].
Proof. by vm_compute. Qed.

Example ex_g2 : radcan_check (sq xm1_3) (RMul (RSub X one) (sq (RSub X one))) =
  Some [:: CGe0 xm1].
Proof. by vm_compute. Qed.

Example ex_g3 :
  radcan_check (sq x4m2x2p1) (RSub (RPow X 2) one) = Some [:: CGe0 x2m1].
Proof. by vm_compute. Qed.

Example ex_g4 : radcan_check (RMul (sq x2p2xp1) (sq xp1)) (RMul xp1 (sq xp1)) =
  Some [:: CGe0 xp1].
Proof. by vm_compute. Qed.

Example ex_g5 :
  radcan_check (sq (RAdd (RAdd (RMul two (RPow X 2)) (RMul four X)) two))
               (RMul xp1 (sqrt_ 2)) = Some [:: CGe0 xp1].
Proof. by vm_compute. Qed.

Example ex_g6 :
  radcan_check (RMul (RSub (RPow X 2) one) (RInv x2p2xp1))
               (RMul (RSub X one) (RInv xp1)) =
  Some [:: CNeq0 xp1].
Proof. by vm_compute. Qed.

Example ex_g7 : radcan_check (sq xy2) (RAdd X Y) = Some [:: CGe0 yx].
Proof. by vm_compute. Qed.

Example ex_g8 :
  radcan_check (cb (RAdd (RAdd (RAdd (RPow X 3) (RMul three (RPow X 2)))
                               (RMul three X)) one))
               xp1 = Some [:: CGe0 xp1].
Proof. by vm_compute. Qed.

Example ex_g9 : radcan_check (sq (RMul Y x2p2xp1)) (RMul xp1 (sq Y)) =
  Some [:: CGe0 Y; CGe0 xp1].
Proof. by vm_compute. Qed.

Example ex_g10 :
  radcan_check (RMul (RSub (RPow X 2) (RPow Y 2)) (RInv xy2))
               (RMul (RSub X Y) (RInv (RAdd X Y)))
  = Some [:: CNeq0 yx].
Proof. by vm_compute. Qed.

(* timings: about 0.005 s each *)
Time Eval vm_compute in radcan_check (sq x2p2xp1) xp1.
Time Eval vm_compute in
  radcan_check (sq xm1_3) (RMul (RSub X one) (sq (RSub X one))).
Time Eval vm_compute in radcan_check (sq x4m2x2p1) (RSub (RPow X 2) one).
Time Eval vm_compute in
  radcan_check (RMul (sq x2p2xp1) (sq xp1)) (RMul xp1 (sq xp1)).
Time Eval vm_compute in
  radcan_check (RMul (RSub (RPow X 2) one) (RInv x2p2xp1))
               (RMul (RSub X one) (RInv xp1)).
Time Eval vm_compute in radcan_check (sq xy2) (RAdd X Y).
(* a larger one: sqrt ((x+1)^4 (x-2)^2 (x^2+y)^3) *)
Time Eval vm_compute in
  radcan_check
    (sq (RMul (RMul (RPow xp1 4) (RPow (RSub X two) 2))
              (RPow (RAdd (RPow X 2) Y) 3)))
    (RMul (RMul (RPow xp1 2) (RSub X two))
          (RMul (RAdd (RPow X 2) Y) (sq (RAdd (RPow X 2) Y)))).

(* Roots of negative numbers through omega_n = proot n (-1), printed
   RRootE n (RCst (-1)) (neg mode, radcan_check_neg) *)
Definition om (n : positive) := RRootE n (neg 1).

(* sqrt (-4) = 2 omega_2 *)
Example ex_w1 :
  radcan_check_neg (sq (neg 4)) (RMul two (om 2)) = Some [::].
Proof. by vm_compute. Qed.

(* sqrt (-1) ^ 2 = -1 *)
Example ex_w2 :
  radcan_check_neg (RPow (sq (neg 1)) 2) (neg 1) = Some [::].
Proof. by vm_compute. Qed.

(* sqrt (-2) sqrt (-8) = -4 for the principal roots *)
Example ex_w3 :
  radcan_check_neg (RMul (sq (neg 2)) (sq (neg 8))) (neg 4) = Some [::].
Proof. by vm_compute. Qed.

(* cbrt (-8) ^ 3 = -8 *)
Example ex_w4 :
  radcan_check_neg (RPow (cb (neg 8)) 3) (neg 8) = Some [::].
Proof. by vm_compute. Qed.

(* cbrt (-8) = 2 cbrt (-1), not -2 for the principal roots *)
Example ex_w5 :
  radcan_check_neg (cb (neg 8)) (RMul two (om 3)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_w5' : radcan_check_neg (cb (neg 8)) (neg 2) = None.
Proof. by vm_compute. Qed.

(* sqrt (-3) ^ 3 = -3 sqrt (-3) *)
Example ex_w6 :
  radcan_check_neg (RMul (RMul (sq (neg 3)) (sq (neg 3))) (sq (neg 3)))
    (RMul (neg 3) (sq (neg 3))) = Some [::].
Proof. by vm_compute. Qed.

(* (1 + sqrt (-1)) ^ 2 = 2 sqrt (-1) *)
Example ex_w7 :
  radcan_check_neg (RPow (RAdd one (sq (neg 1))) 2) (RMul two (sq (neg 1))) =
  Some [::].
Proof. by vm_compute. Qed.

(* 1 / sqrt (-1) = - sqrt (-1): omega_n ^-1 = - omega_n ^+ (n - 1) *)
Example ex_w8 :
  radcan_check_neg (RInv (sq (neg 1))) (ROpp (sq (neg 1))) = Some [::].
Proof. by vm_compute. Qed.

(* 1 / cbrt (-2) = - cbrt (-1) ^ 2 cbrt 4 / 2 *)
Example ex_w9 : radcan_check_neg (RInv (cb (neg 2)))
  (RMul (neg 1) (RMul (RMul (RPow (om 3) 2) (cb four)) (RInv two))) = Some [::].
Proof. by vm_compute. Qed.

(* sqrt (- (x - 1) ^ 2) = (x - 1) omega_2 when 0 <= x - 1 *)
Example ex_w10 :
  radcan_check_neg (sq (ROpp (RPow xm1' 2))) (RMul xm1' (om 2)) =
  Some [:: CGe0 xm1].
Proof. by vm_compute. Qed.

(* the main checker and the odd mode reject them: no answer, or an
   unprovable condition 0 <= -a *)
Example ex_w1_main : radcan_check (sq (neg 4)) (RMul two (om 2)) = None.
Proof. by vm_compute. Qed.
Example ex_w2_main :
  radcan_check (RPow (sq (neg 1)) 2) (neg 1) = Some [:: CGe0 (RCst (-1))].
Proof. by vm_compute. Qed.
Example ex_w3_main :
  radcan_check (RMul (sq (neg 2)) (sq (neg 8))) (neg 4) = None.
Proof. by vm_compute. Qed.
Example ex_w4_main :
  radcan_check (RPow (cb (neg 8)) 3) (neg 8) = Some [:: CGe0 (RCst (-8))].
Proof. by vm_compute. Qed.
Example ex_w5_main : radcan_check (cb (neg 8)) (RMul two (om 3)) = None.
Proof. by vm_compute. Qed.
Example ex_w6_main :
  radcan_check (RMul (RMul (sq (neg 3)) (sq (neg 3))) (sq (neg 3)))
    (RMul (neg 3) (sq (neg 3))) = Some [:: CGe0 (RCst (-3))].
Proof. by vm_compute. Qed.
Example ex_w7_main :
  radcan_check (RPow (RAdd one (sq (neg 1))) 2) (RMul two (sq (neg 1))) =
  Some [:: CGe0 (RCst (-1))].
Proof. by vm_compute. Qed.
Example ex_w2_odd : radcan_check_odd (RPow (sq (neg 1)) 2) (neg 1) =
  Some [:: CGe0 (RCst (-1))].
Proof. by vm_compute. Qed.

(* timings: about 0.001 s each *)
Time Eval vm_compute in radcan_check_neg (sq (neg 4)) (RMul two (om 2)).
Time Eval vm_compute in
  radcan_check_neg (RMul (sq (neg 2)) (sq (neg 8))) (neg 4).
Time Eval vm_compute in
  radcan_check_neg (RMul (RMul (sq (neg 3)) (sq (neg 3))) (sq (neg 3)))
                   (RMul (neg 3) (sq (neg 3))).
Time Eval vm_compute in
  radcan_check_neg (RPow (RAdd one (sq (neg 1))) 2) (RMul two (sq (neg 1))).

(* in a field with roots of unity *)
Example ex_field_w1 (F : numFieldType) (r : posroot F) (w : negroot r) :
  proot r 2 (- 2) * proot r 2 (- 8) = - 4.
Proof.
apply: (@radcan_eq_neg F r w [::] (RMul (sq (neg 2)) (sq (neg 8))) (neg 4)).
by vm_compute.
Qed.

(* Inverse atoms: cancelled as many times as their exponent (x^3 / x^3),
   primitive with a positive leading coefficient ((2x + 2)^-1 =
   1/2 (x + 1)^-1), common root monomials inverted apart, exact division of
   numerators with root monomials ((sqrt 2 x + sqrt 2) / (x + 1)) *)
Definition r2 := sqrt_ 2.

Example ex_m1 :
  radcan_check (RMul (RPow X 3) (RInv (RPow X 3))) one = Some [:: CNeq0 X].
Proof. by vm_compute. Qed.

Example ex_m2 :
  radcan_check (RMul (RMul X X) (RInv (RMul X X))) one = Some [:: CNeq0 X].
Proof. by vm_compute. Qed.

Example ex_m3 :
  radcan_check (RMul (RMul (RPow X 3) Y) (RInv (RMul (RPow X 3) Y))) one =
  Some [:: CNeq0 X; CNeq0 Y].
Proof. by vm_compute. Qed.

(* the same with a root somewhere (radcan_check_root path) *)
Example ex_m3r :
  radcan_check (RMul (RMul (RPow X 3) Y) (RInv (RMul (RPow X 3) Y)))
               (RSub (RAdd one r2) r2) =
  Some [:: CNeq0 X; CNeq0 Y].
Proof. by vm_compute. Qed.

Example ex_m4 : radcan_check (RMul (RPow X 2) (RInv X)) X = Some [:: CNeq0 X].
Proof. by vm_compute. Qed.

Example ex_m5 :
  radcan_check (RMul X (RInv (RPow X 2))) (RInv X) = Some [:: CNeq0 X].
Proof. by vm_compute. Qed.

Example ex_m6 :
  radcan_check (RMul (RPow X 2) (RInv (RPow X 5))) (RInv (RPow X 3)) =
  Some [:: CNeq0 X].
Proof. by vm_compute. Qed.

(* sqrt (x/2 - 1) ^ 2 = x/2 - 1: the radicand is 1/2 (x - 2) *)
Definition xh := RSub (RMul X (RInv two)) one.
Example ex_m7 :
  radcan_check (RPow (sq xh) 2) xh = Some [:: CGe0 (RAdd X (RCst (-2)))].
Proof. by vm_compute. Qed.

Definition tx2 := RAdd (RMul two X) two.
Example ex_m8 :
  radcan_check (RInv tx2) (RMul (RInv two) (RInv xp1)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_m9 : radcan_check (RMul tx2 (RInv xp1)) two = Some [:: CNeq0 xp1].
Proof. by vm_compute. Qed.

Example ex_m10 :
  radcan_check (RMul xp1 (RInv tx2)) (RInv two) = Some [:: CNeq0 xp1].
Proof. by vm_compute. Qed.

Example ex_m11 : radcan_check (RInv omx) (ROpp (RInv xm1')) = Some [::].
Proof. by vm_compute. Qed.

Example ex_m12 : radcan_check (RMul tx2 (RInv (RAdd (RMul three X) three)))
                              (RMul two (RInv three)) = Some [:: CNeq0 xp1].
Proof. by vm_compute. Qed.

(* 1 / (x * y) = (1 / x) (1 / y) (invfM, no condition) *)
Example ex_m13 :
  radcan_check (RInv (RMul X Y)) (RMul (RInv X) (RInv Y)) = Some [::].
Proof. by vm_compute. Qed.

Example ex_m14 :
  radcan_check (RInv (RAdd (RMul r2 X) r2)) (RMul r2 (RInv (RMul two xp1))) =
  Some [::].
Proof. by vm_compute. Qed.

Example ex_m15 : radcan_check (RMul (RAdd (RMul r2 X) r2) (RInv xp1)) r2 =
  Some [:: CNeq0 xp1].
Proof. by vm_compute. Qed.

Example ex_m16 : radcan_check (RMul X (RInv (RMul r2 X))) (RMul r2 (RInv two)) =
  Some [:: CNeq0 X].
Proof. by vm_compute. Qed.

(* timings: at most 0.002 s each *)
Time Eval vm_compute in radcan_check (RMul (RPow X 3) (RInv (RPow X 3))) one.
Time Eval vm_compute in
  radcan_check (RMul (RMul (RPow X 3) Y) (RInv (RMul (RPow X 3) Y)))
               (RSub (RAdd one r2) r2).
Time Eval vm_compute in radcan_check (RPow (sq xh) 2) xh.
Time Eval vm_compute in radcan_check (RInv tx2) (RMul (RInv two) (RInv xp1)).
Time Eval vm_compute in radcan_check (RMul tx2 (RInv xp1)) two.
Time Eval vm_compute in
  radcan_check (RMul (RAdd (RMul r2 X) r2) (RInv xp1)) r2.
Time Eval vm_compute in
  radcan_check (RMul (RPow X 10) (RInv (RPow X 10))) (RSub (RAdd one r2) r2).

Print Assumptions radcan_eq_cond.
Print Assumptions radcan_eq_cond0.
Print Assumptions radcan_eq_cond_odd.
Print Assumptions radcan_eq_cond_neg.

(* M11: denominators mixing variables and roots (Ratio.v).  nf_rat_inv d    *)
(* gives (u, E) with d * u = E, E root-free, primitive, positive leading    *)
(* coefficient                                                               *)
Definition rd1 := RAdd (sq X) (sq Y).
Definition rd2 := RAdd one (sq X).
Definition rd3 := RAdd X r2.
Definition rd4 := RAdd (RAdd X r2) (RRoot 3 9).
Definition rd5 := RAdd (RAdd (sq X) (sq Y)) r2.

Time Eval vm_compute in nf_rat_inv (pnorm rd1).
Time Eval vm_compute in nf_rat_inv (pnorm rd2).
Time Eval vm_compute in nf_rat_inv (pnorm rd3).
Time Eval vm_compute in nf_rat_inv (pnorm rd4).
Time Eval vm_compute in nf_rat_inv (pnorm rd5).

(* timings: 0.005, 0.002, 0.002, 0.03 and 0.09 s *)

Example ex_ratio1 :
  radcan_check (RMul (RSub X Y) (RInv rd1)) (RSub (sq X) (sq Y)) =
  Some [:: CGe0 X; CGe0 Y; CNeq0 (RAdd (RMul (RCst (-1)) Y) X)].
Proof. by vm_compute. Qed.

Example ex_ratio2 :
  radcan_check (RInv rd2) (RMul (RSub one (sq X)) (RInv omx)) =
  Some [:: CNeq0 (RAdd X (RCst (-1))); CGe0 X].
Proof. by vm_compute. Qed.

Example ex_ratio3 :
  radcan_check (RInv rd3) (RMul (RSub X r2) (RInv (RSub (RPow X 2) two))) =
  Some [:: CNeq0 (RAdd (RPow X 2) (RCst (-2)))].
Proof. by vm_compute. Qed.

(* timings: 0.009, 0.004 and 0.002 s *)
Time Eval vm_compute in
  radcan_check (RMul (RSub X Y) (RInv rd1)) (RSub (sq X) (sq Y)).
Time Eval vm_compute in
  radcan_check (RInv rd2) (RMul (RSub one (sq X)) (RInv omx)).
Time Eval vm_compute in
  radcan_check (RInv rd3) (RMul (RSub X r2) (RInv (RSub (RPow X 2) two))).
