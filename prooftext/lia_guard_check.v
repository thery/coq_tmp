(* Tests of lia_guard (Tactics.v): its counts (case splits, cases,
   hypotheses read by lia) on goals of each shape, the goals lia proves,
   and a goal it refuses.
   rocq c -Q ../lexicon Lexicon -Q . ProofText lia_guard_check.v *)
From ProofText Require Import Tactics.
From Stdlib Require Import ZArith Reals Lia Lra.

(* zify's intros: the premises are hypotheses; one atom each; the goal's
   equality is two cases *)
Goal forall n : nat, n + 0 = n.
Proof. lia_expect 1 2 0. guarded_lia. Qed.
Goal forall n m : nat, n <= m -> n < S m.
Proof. lia_expect 0 1 1. guarded_lia. Qed.
(* a disjunction of hypotheses, a disequality, a conjunction of the goal *)
Goal forall a b c : Z, (a <= b \/ b <= c)%Z -> (a = 0 \/ b = 0)%Z -> a <> c -> a = b /\ b = c.
Proof. lia_expect 5 32 3. Abort.
(* Z.abs: one hypothesis of two cases per distinct term; Z.sub no case *)
Goal forall k : Z, (Z.abs (k * 16 - 5) <= 12 -> Z.abs (k * 16 - 5) <= 11)%Z.
Proof. lia_expect 1 2 1. guarded_lia. Qed.
(* the truncated subtraction of nat and Z.to_nat: two cases each *)
Goal forall n m : nat, n - m + Z.to_nat (Z.abs 3) = 0 -> n <= m.
Proof. lia_expect 3 8 1. guarded_lia. Qed.
(* what lia does not read: a hypothesis on R, a forall, an unknown
   proposition (it makes the formula around it useless) *)
Goal forall (x y : R) (P : Prop) (k : Z), (x < y)%R -> (forall z : Z, z < 10)%Z ->
  (P -> k <= 0)%Z -> (k > 0 \/ P)%Z -> (k = 1)%Z /\ True.
Proof. lia_expect 1 2 0. Abort.
(* the shape of cyp/examples/forall_premise.md: a premise on all the
   integers k after eighteen facts on reals, which lia does not read *)
Goal forall (x y : R),
  (0 < y)%R -> (0 < y + 1)%R -> (0 < y + 2)%R -> (0 < y + 3)%R -> (0 < y + 4)%R ->
  (0 < y + 5)%R -> (0 < y + 6)%R -> (0 < y + 7)%R -> (0 < y + 8)%R -> (0 < y + 9)%R ->
  (0 < y + 10)%R -> (0 < y + 11)%R -> (0 < y + 12)%R -> (0 < y + 13)%R ->
  (0 < y + 14)%R -> (0 < y + 15)%R -> (0 < y + 16)%R -> (Rabs x <= 12)%R ->
  forall k : Z, (Z.abs (k * 2 ^ 4 - -5) <= 12 -> Z.abs (k * 2 ^ 4 - -5) <= 11)%Z.
Proof. intros. lia_expect 1 2 1. guarded_lia. Qed.
(* refused: a hypothesis that is a conjunction of 51 disjunctions, 2^51 cases *)
Goal forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 : Z, ((x1 <= 0 \/ x1 >= 2) /\ (x2 <= 0 \/ x2 >= 2) /\ (x3 <= 0 \/ x3 >= 2) /\ (x4 <= 0 \/ x4 >= 2) /\ (x5 <= 0 \/ x5 >= 2) /\ (x6 <= 0 \/ x6 >= 2) /\ (x7 <= 0 \/ x7 >= 2) /\ (x8 <= 0 \/ x8 >= 2) /\ (x9 <= 0 \/ x9 >= 2) /\ (x10 <= 0 \/ x10 >= 2) /\ (x11 <= 0 \/ x11 >= 2) /\ (x12 <= 0 \/ x12 >= 2) /\ (x13 <= 0 \/ x13 >= 2) /\ (x14 <= 0 \/ x14 >= 2) /\ (x15 <= 0 \/ x15 >= 2) /\ (x16 <= 0 \/ x16 >= 2) /\ (x17 <= 0 \/ x17 >= 2) /\ (x18 <= 0 \/ x18 >= 2) /\ (x19 <= 0 \/ x19 >= 2) /\ (x20 <= 0 \/ x20 >= 2) /\ (x21 <= 0 \/ x21 >= 2) /\ (x22 <= 0 \/ x22 >= 2) /\ (x23 <= 0 \/ x23 >= 2) /\ (x24 <= 0 \/ x24 >= 2) /\ (x25 <= 0 \/ x25 >= 2) /\ (x26 <= 0 \/ x26 >= 2) /\ (x27 <= 0 \/ x27 >= 2) /\ (x28 <= 0 \/ x28 >= 2) /\ (x29 <= 0 \/ x29 >= 2) /\ (x30 <= 0 \/ x30 >= 2) /\ (x31 <= 0 \/ x31 >= 2) /\ (x32 <= 0 \/ x32 >= 2) /\ (x33 <= 0 \/ x33 >= 2) /\ (x34 <= 0 \/ x34 >= 2) /\ (x35 <= 0 \/ x35 >= 2) /\ (x36 <= 0 \/ x36 >= 2) /\ (x37 <= 0 \/ x37 >= 2) /\ (x38 <= 0 \/ x38 >= 2) /\ (x39 <= 0 \/ x39 >= 2) /\ (x40 <= 0 \/ x40 >= 2) /\ (x41 <= 0 \/ x41 >= 2) /\ (x42 <= 0 \/ x42 >= 2) /\ (x43 <= 0 \/ x43 >= 2) /\ (x44 <= 0 \/ x44 >= 2) /\ (x45 <= 0 \/ x45 >= 2) /\ (x46 <= 0 \/ x46 >= 2) /\ (x47 <= 0 \/ x47 >= 2) /\ (x48 <= 0 \/ x48 >= 2) /\ (x49 <= 0 \/ x49 >= 2) /\ (x50 <= 0 \/ x50 >= 2) /\ (x51 <= 0 \/ x51 >= 2) /\  True)%Z -> False.
Proof. intros. lia_expect 51 2251799813685248 1. Fail lia_guard. Abort.
