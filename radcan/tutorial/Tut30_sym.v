(******************************************************************************)
(* Tutorial 30 (M15): roots given by hypotheses, the paper's reading.         *)
(* The paper (§3) treats radicals as formal generators of a field extension:  *)
(* (x - 1)^(1/2) is "some y with y^2 = x - 1", not a branch of a root         *)
(* function.  radcan_sym (SymTac.v) does exactly that: the user introduces    *)
(* his own symbols with defining equations                                    *)
(*     hy : y ^+ n = B     or     hz : z = B                                  *)
(* and the goal is proved for EVERY choice of such symbols.  In the           *)
(* normaliser (Sym.v) a symbol is a variable reduced only by y ^+ n -> B      *)
(* (exponents taken mod n) and y^-1 -> y ^+ n.-1 * B^-1: no multiplicativity, *)
(* no merging, no sign law, no branch, so no side condition beyond the        *)
(* cancellations B != 0 of a division.                                        *)
(*   radcan_eq_cond_sym : radcan_check_sym rels e1 e2 = Some cs ->            *)
(*      rels_hold rt env rels -> all_conds_gen rt env cs ->                   *)
(*      rinterp_gen rt env e1 = rinterp_gen rt env e2      (any rt)           *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan Tactic Sym SymTac.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Sym.
Variables (F : numFieldType) (x : F).
(* y = (x - 1)^(1/2), z = (1 - x)^(1/4), w = (-1)^(1/4): any choice *)
Variables (y : F) (z : F) (w : F).
Hypotheses (hy : y ^+ 2 = x - 1) (hz : z ^+ 4 = 1 - x) (hw : w ^+ 4 = -1).

Lemma sym1 : y ^+ 3 = (x - 1) * y.
Proof. radcan_sym. Qed.

Lemma sym2 : (y + 1) ^+ 2 = x + 2 * y.
Proof. radcan_sym. Qed.

Lemma sym3 : z ^+ 4 + y ^+ 2 = 0.
Proof. radcan_sym. Qed.

(* inverses need no condition: y^-1 = y * (y ^+ 2)^-1 even for y = 0 *)
Lemma sym4 : y^-1 = y / (x - 1).
Proof. radcan_sym. Qed.

Lemma sym5 : w ^+ 8 = 1.
Proof. radcan_sym. Qed.

(* sqrt 2 in the paper's reading is w - w^3 (a primitive 8-th root w) *)
Lemma sym6 : (w - w ^+ 3) ^+ 2 = 2.
Proof. radcan_sym. Qed.

(* two symbols with the same relation are different: v may be - y *)
Variables (v : F) (hv : v ^+ 2 = x - 1).
Lemma sym7 : v ^+ 2 = y ^+ 2.
Proof. radcan_sym. Qed.
Goal v = y.
Proof. Fail radcan_sym. Abort.
Lemma sym8 : (v - y) * (v + y) = 0.
Proof. radcan_sym. Qed.
End Sym.

(* The paper's (2): (x-1)^(1/4) / (1-x)^(1/4) - (x-1)^(3/4) / (1-x)^(3/4)
   - sqrt 2 = 0.  Its reading: u = (x-1)^(1/4), (1-x)^(1/4) = w u with
   w = (-1)^(1/4), (x-1)^(3/4) = u^3, (1-x)^(3/4) = (w u)^3, and sqrt 2 the
   element w - w^3 of the extension (sym6).  The cancellation u / u needs
   u != 0, i.e. x != 1, which the paper leaves implicit (for x = 1 the left
   side is - sqrt 2). *)
Section Paper2.
Variables (F : numFieldType) (x u w z : F).
Hypotheses (hu : u ^+ 4 = x - 1) (hw : w ^+ 4 = -1) (hz : z = w * u).

Lemma z4 : z ^+ 4 = 1 - x.
Proof. radcan_sym. Qed.

Lemma paper2 : x != 1 ->
  u / z - u ^+ 3 / z ^+ 3 - (w - w ^+ 3) = 0.
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.

(* without the relation z = w u, z is any fourth root of 1 - x: refused *)
Goal forall z' : F, z' ^+ 4 = 1 - x -> x != 1 ->
  u / z' - u ^+ 3 / z' ^+ 3 - (w - w ^+ 3) = 0.
Proof. move=> z' hz' h. Fail radcan_sym. Abort.
End Paper2.

(* the symbols live in any field, e.g. C; genuine roots stay opaque atoms *)
Section OnC.
Variables (C : numClosedFieldType) (x s : C).
Hypothesis hs : s ^+ 3 = x + 1.

Lemma symC : (s ^+ 2) ^+ 2 = (x + 1) * s.
Proof. radcan_sym. Qed.
End OnC.
