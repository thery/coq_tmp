(******************************************************************************)
(* Radcan: the normaliser RadcanF N over a number backend N : NUM, built in   *)
(*   Backend.v  numbers (Q2F, NUM, ZNum)    Mono.v     monomials, orders      *)
(*   Factor.v   constant radicands          NF.v       normal forms, pnorm    *)
(*   Inverse.v  inverses (checked)          Poly.v     polynomial radicands   *)
(*   Cond.v     normaliser with side conditions, checkers, soundness          *)
(* and instantiated on Stdlib Z / Q (BigBackend.v, RadcanBig.v: Bignums):     *)
(*   RadcanZ := RadcanF ZNum, exported: radcan_check, radcan_eq_cond, ...     *)
(* Main theorems (Cond.v), for r : posroot F and conditions from Syntax.v:    *)
(*   radcan_eq_cond  : radcan_check e1 e2 = Some cs -> all_conds r env cs ->  *)
(*                     rinterp r env e1 = rinterp r env e2                    *)
(*   radcan_eq_cond0 : the same for root-free e1 e2 with rinterp0, all_conds0 *)
(*   radcan_eq_cond_odd (o : oddroot r), radcan_eq_cond_neg (w : negroot r),  *)
(*   radcan_eq_cond_real (rl : realroot r): the same with radcan_check_odd,   *)
(*                     radcan_check_neg, radcan_check_real                    *)
(******************************************************************************)

From Radcan Require Export Backend Mono Factor NF Inverse Poly Cond.

Module RadcanZ := RadcanF ZNum.
Export RadcanZ.
