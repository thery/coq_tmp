From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC RootR Syntax Tactic.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Goal forall (F : numFieldType) (r : posroot F),
  (1 + proot r 2 2) ^+ 2 - 3 = 2 * proot r 2 2.
Proof. move=> F r. let r := radcan_find_root in radcan_reify r. Show. Abort.

Goal forall (C : numClosedFieldType), 2.-root 2 * 2.-root 3 = 2.-root (6 : C).
Proof. move=> C. let r := radcan_find_root in radcan_reify r. Show. Abort.

Goal forall (R : rcfType), rootR 2 2 * rootR 2 3 = rootR 2 (6 : R).
Proof. move=> R. let r := radcan_find_root in radcan_reify r. Show. Abort.
