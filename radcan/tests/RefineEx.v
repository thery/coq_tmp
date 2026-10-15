(******************************************************************************)
(* RefineEx: examples of the refinement (refine_ex*, implied_ex,              *)
(*   refine_example).                                                         *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan Refine.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* Examples *)

Definition X := RVar 0.
Definition Y := RVar 1.
Definition xp1 := RAdd X (RCst 1).
Definition xm1 := RAdd X (RCst (-1)).

(* 0 <= x+1, 0 <= x-1, x-1 != 0  ~>  1 < x *)
Example refine_ex1 : refine [:: CGe0 xp1; CGe0 xm1; CNeq0 xm1] =
  [:: RLow true (false, 1%N, 1%N) 0%N].
Proof. by vm_compute. Qed.

(* 0 <= x  ~>  0 <= x *)
Example refine_ex2 : refine [:: CGe0 X] =
  [:: RLow false (false, 0%N, 1%N) 0%N].
Proof. by vm_compute. Qed.

(* 0 <= x+1, 0 <= x-1  ~>  1 <= x *)
Example refine_ex3 : refine [:: CGe0 xp1; CGe0 xm1] =
  [:: RLow false (false, 1%N, 1%N) 0%N].
Proof. by vm_compute. Qed.

(* x+1 != 0, x-1 != 0  ~>  x != -1, x != 1 *)
Example refine_ex4 : refine [:: CNeq0 xp1; CNeq0 xm1] =
  [:: RNeq 0 (true, 1%N, 1%N); RNeq 0 (false, 1%N, 1%N)].
Proof. by vm_compute. Qed.

(* 0 <= x, 0 <= y  ~>  0 <= x, 0 <= y *)
Example refine_ex5 : refine [:: CGe0 X; CGe0 Y] =
  [:: RLow false (false, 0%N, 1%N) 0%N; RLow false (false, 0%N, 1%N) 1%N].
Proof. by vm_compute. Qed.

(* not affine: 0 <= x*y + 1  ~>  -1 <= x*y *)
Example refine_ex6 : refine [:: CGe0 (RAdd (RMul X Y) (RCst 1))] =
  [:: RCmp false [:: ((true, 1%N, 1%N), [::])]
        [:: ((false, 1%N, 1%N), [:: (RVar 0, 1%N); (RVar 1, 1%N)])]].
Proof. by vm_compute. Qed.

(* 0 <= 3 is dropped *)
Example refine_ex7 : refine [:: CGe0 (RCst 3)] =
  [::].
Proof. by vm_compute. Qed.

(* 0 <= 1-2x, 3x != 0, 2x-1 != 0  ~>  x < 1/2, x != 0 *)
Example refine_ex8 :
  refine [:: CGe0 (RSub (RCst 1) (RMul (RCst 2) X)); CNeq0 (RMul (RCst 3) X);
             CNeq0 (RAdd (RMul (RCst 2) X) (RCst (-1)))] =
  [:: RUpp true (false, 1%N, 2%N) 0%N; RNeq 0 (false, 0%N, 1%N)].
Proof. by vm_compute. Qed.

(* 0 <= 3x+2, 0 <= x+2/3 (duplicate bound)  ~>  -2/3 <= x *)
Example refine_ex9 :
  refine [:: CGe0 (RAdd (RMul (RCst 3) X) (RCst 2));
             CGe0 (RAdd X (RMul (RCst 2) (RInv (RCst 3))))] =
  [:: RLow false (true, 2%N, 3%N) 0%N].
Proof. by vm_compute. Qed.

(* several variables *)
Definition vx : amono := [:: (RVar 0, 1%N)].
Definition vy : amono := [:: (RVar 1, 1%N)].
Definition one : bound := (false, 1%N, 1%N).

(* 0 <= -1*y + x  ~>  y <= x *)
Example refine_ex10 : refine [:: CGe0 (RAdd (RMul (RCst (-1)) Y) X)] =
  [:: RCmp false [:: (one, vy)] [:: (one, vx)]].
Proof. by vm_compute. Qed.

(* x - y != 0  ~>  x != y *)
Example refine_ex11 : refine [:: CNeq0 (RSub X Y)] =
  [:: RDiff [:: (one, vx)] [:: (one, vy)]].
Proof. by vm_compute. Qed.

(* 0 <= 2x - 2y  ~>  y <= x;  0 <= 2x - 2y + 1  ~>  2y - 1 <= 2x *)
Example refine_ex12 :
  refine [:: CGe0 (RSub (RMul (RCst 2) X) (RMul (RCst 2) Y))] =
  [:: RCmp false [:: (one, vy)] [:: (one, vx)]].
Proof. by vm_compute. Qed.

Example refine_ex12' :
  refine [:: CGe0 (RAdd (RSub (RMul (RCst 2) X) (RMul (RCst 2) Y)) (RCst 1))] =
  [:: RCmp false [:: ((false, 2%N, 1%N), vy); ((true, 1%N, 1%N), [::])]
                 [:: ((false, 2%N, 1%N), vx)]].
Proof. by vm_compute. Qed.

(* x^3 * y != 0  ~>  x != 0, y != 0 *)
Example refine_ex13 : refine [:: CNeq0 (RMul (RPow X 3) Y)] =
  [:: RNeq 0 (false, 0%N, 1%N); RNeq 1 (false, 0%N, 1%N)].
Proof. by vm_compute. Qed.

(* (x-1) * (x+1) != 0  ~>  x != 1, x != -1 *)
Example refine_ex14 :
  refine [:: CNeq0 (RMul (RAdd X (RCst (-1))) (RAdd X (RCst 1)))] =
  [:: RNeq 0 (false, 1%N, 1%N); RNeq 0 (true, 1%N, 1%N)].
Proof. by vm_compute. Qed.

(* 0 <= x^2 - 1, x^2 - 4 != 0  ~>  1 <= x^2, x^2 != 4 *)
Example refine_ex15 :
  refine [:: CGe0 (RSub (RPow X 2) (RCst 1));
             CNeq0 (RSub (RPow X 2) (RCst 4))] =
  [:: RCmp false [:: (one, [::])] [:: (one, [:: (RVar 0, 2%N)])];
      RDiff [:: (one, [:: (RVar 0, 2%N)])] [:: ((false, 4%N, 1%N), [::])]].
Proof. by vm_compute. Qed.

(* implied duplicate: 0 <= x - y, 0 <= 2x - 2y + 1, 0 <= x + y
   ~>  y <= x, 0 <= x + y *)
Example refine_ex16 :
  refine [:: CGe0 (RSub X Y);
             CGe0 (RAdd (RSub (RMul (RCst 2) X) (RMul (RCst 2) Y)) (RCst 1));
             CGe0 (RAdd X Y)] =
  [:: RCmp false [:: (one, vy)] [:: (one, vx)];
      RCmp false [::] [:: (one, vx); (one, vy)]].
Proof. by vm_compute. Qed.

(* merge: 0 <= 3 - (x+y), x + y - 3 != 0  ~>  x + y < 3 *)
Example refine_ex17 :
  refine [:: CGe0 (RSub (RCst 3) (RAdd X Y));
             CNeq0 (RSub (RAdd X Y) (RCst 3))] =
  [:: RCmp true [:: (one, vx); (one, vy)] [:: ((false, 3%N, 1%N), [::])]].
Proof. by vm_compute. Qed.

(* atoms other than variables: 0 <= sqrt x, sqrt x != 0  ~>  0 < sqrt x *)
Example refine_ex18 : refine [:: CGe0 (RRootE 2 X); CNeq0 (RRootE 2 X)] =
  [:: RCmp true [::] [:: (one, [:: (RRootE 2 (RVar 0), 1%N)])]].
Proof. by vm_compute. Qed.

(* 0 <= y + x, 0 <= -1*y + x, -1*y + x != 0  ~>  0 <= x + y, y < x *)
Example refine_ex19 :
  refine [:: CGe0 (RAdd Y X); CGe0 (RAdd (RMul (RCst (-1)) Y) X);
             CNeq0 (RAdd (RMul (RCst (-1)) Y) X)] =
  [:: RCmp false [::] [:: (one, vx); (one, vy)];
      RCmp true [:: (one, vy)] [:: (one, vx)]].
Proof. by vm_compute. Qed.

(* sqrt(x^2-1) / sqrt(x-1) = sqrt(x+1) *)
Example radcan_check_ex :
  radcan_check (RMul (RRootE 2 (RSub (RPow X 2) (RCst 1)))
                     (RInv (RRootE 2 (RSub X (RCst 1)))))
               (RRootE 2 (RAdd X (RCst 1))) =
  Some [:: CGe0 xp1; CGe0 xm1; CNeq0 xm1].
Proof. by vm_compute. Qed.

Lemma refine_example (F : numFieldType) (r : posroot F) (x : F) : 1 < x ->
  rinterp r [:: x]
    (RMul (RRootE 2 (RSub (RPow X 2) (RCst 1)))
          (RInv (RRootE 2 (RSub X (RCst 1))))) =
  rinterp r [:: x] (RRootE 2 (RAdd X (RCst 1))).
Proof.
move=> x_gt1.
apply: (@radcan_eq_refined F r [:: x] _ _ _
          [:: RLow true (false, 1%N, 1%N) 0%N]).
- by vm_compute.
- by vm_compute.
rewrite /=. (* 1 < x *)
exact: x_gt1.
Qed.

(* intervals: 0 <= x - 1, 0 <= 3 - x  ~>  1 <= x <= 3 *)
Example refine_ex20 :
  refine [:: CGe0 (RSub X (RCst 1)); CGe0 (RSub (RCst 3) X)] =
  [:: RInt false one 0 false (false, 3%N, 1%N)].
Proof. by vm_compute. Qed.

(* 0 <= x - 1, 0 <= 3 - x, x - 3 != 0, 0 <= 4 - x  ~>  1 <= x < 3 *)
Example refine_ex21 :
  refine [:: CGe0 (RSub X (RCst 1)); CGe0 (RSub (RCst 3) X);
             CNeq0 (RSub X (RCst 3)); CGe0 (RSub (RCst 4) X)] =
  [:: RInt false one 0 true (false, 3%N, 1%N)].
Proof. by vm_compute. Qed.

(* combinations: 0 <= x - 1, 0 <= y - 2, 0 <= x + y - 3, 0 <= 2x + y,
   x + y - 2 != 0  ~>  1 <= x, 2 <= y *)
Example refine_ex22 :
  refine [:: CGe0 (RSub X (RCst 1)); CGe0 (RSub Y (RCst 2));
             CGe0 (RSub (RAdd X Y) (RCst 3));
             CGe0 (RAdd (RMul (RCst 2) X) Y);
             CNeq0 (RSub (RAdd X Y) (RCst 2))] =
  [:: RLow false one 0; RLow false (false, 2%N, 1%N) 1].
Proof. by vm_compute. Qed.

(* 0 <= x - y, 0 <= y - 1, 0 < x + y - 1  ~>  y <= x, 1 <= y
   (x + y - 1 = (x - y) + 2 (y - 1) + 1) *)
Example refine_ex23 :
  refine [:: CGe0 (RSub X Y); CGe0 (RSub Y (RCst 1));
             CGe0 (RSub (RAdd X Y) (RCst 1));
             CNeq0 (RSub (RAdd X Y) (RCst 1))] =
  [:: RLow false one 1; RCmp false [:: (one, vy)] [:: (one, vx)]].
Proof. by vm_compute. Qed.

(* contradictory bounds are kept: 0 <= x - 3, 0 <= 1 - x  ~>  3 <= x <= 1 *)
Example refine_ex24 :
  refine [:: CGe0 (RSub X (RCst 3)); CGe0 (RSub (RCst 1) X)] =
  [:: RInt false (false, 3%N, 1%N) 0 false one].
Proof. by vm_compute. Qed.

(* equal bounds stay apart: 0 <= x - 1, 0 <= 1 - x  ~>  1 <= x, x <= 1 *)
Example refine_ex25 :
  refine [:: CGe0 (RSub X (RCst 1)); CGe0 (RSub (RCst 1) X)] =
  [:: RLow false one 0; RUpp false one 0].
Proof. by vm_compute. Qed.

(* the checker alone: 0 <= 4 - x follows from 1 <= x <= 3 *)
Example implied_ex :
  implied [:: RInt false one 0 false (false, 3%N, 1%N)]
          (CGe0 (RSub (RCst 4) X)).
Proof. by vm_compute. Qed.
