(******************************************************************************)
(* Tutorial 5: reification of goals on Stdlib's R (radcan_Rstd).              *)
(******************************************************************************)

From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Tactic RootRstd.

Open Scope R_scope.

Goal sqrt 2 * sqrt 3 = sqrt 6.
Proof. radcan_Rstd. let r := radcan_find_root in radcan_reify r. Show. Abort.

Goal (1 + sqrt 2) ^ 2 - 3 = 2 * sqrt 2.
Proof. radcan_Rstd. let r := radcan_find_root in radcan_reify r. Show. Abort.
