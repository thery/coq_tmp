(******************************************************************************)
(* Tutorial 35: a trigonometric identity through C and radcan.               *)
(* IMO 1963, problem 5: cos(pi/7) - cos(2pi/7) + cos(3pi/7) = 1/2, on the    *)
(* reals of the Rocq standard library.  We go to C = R[i] (mathcomp          *)
(* real-closed), where z = cos(pi/7) + i sin(pi/7) satisfies z^7 = -1 and    *)
(* z <> -1, hence Phi_14(z) = 0; the identity is then pure algebra in z,     *)
(* proved by radcan_sym, and we come back to R by taking real parts.         *)
(* Second part: z is mathcomp's principal root 7.-root (-1) (z_root, from    *)
(* the general E_rootZ of trig/TrigBridge.v); then plain radcan proves the   *)
(* identity on 7.-root (-1) (imo1963_omega).                                 *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.real_closed Require Import complex.
From Radcan Require Import Rstruct PosRoot Syntax Radcan Tactic Sym SymTac.
From Radcan Require Import UnitArc.
From RadcanTrig Require Import TrigBridge.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope complex_scope.

(* E x = cos x + i sin x and its laws EE, EM (E (x + y) = E x * E y), EX
   (de Moivre), EN, ENE (E x + E (- x) = 2 cos x) come from
   trig/TrigBridge.v. *)

Delimit Scope ring_scope with RR.
Delimit Scope R_scope with R.

Definition t : R := PI / 7.
Definition z := E t.

Lemma z7 : z ^+ 7 = -1.
Proof.
rewrite /z EX EE.
have -> : (INR 7 * t)%R = PI by rewrite /t /=; field.
by rewrite cos_PI sin_PI rmorph0 mulr0 addr0 rmorphN1.
Qed.

Lemma Ezk k : E (INR k * t) = z ^+ k.
Proof. by rewrite /z EX. Qed.

(* e^(-ikt) = - z^(7-k), since z^7 = -1 *)
Lemma Enk k : (k <= 7)%N -> E (-(INR k * t)) = - z ^+ (7 - k).
Proof.
move=> hk.
have h1 : z ^+ k * E (- (INR k * t)) = 1 by rewrite -Ezk EN.
have h2 : z ^+ (7 - k) * z ^+ k = -1 by rewrite -exprD subnK // z7.
by rewrite -[RHS]mulr1 -h1 mulNr mulrA h2 mulN1r opprK.
Qed.

(* z is a root of Phi_14 = (X^7 + 1) / (X + 1) *)
Lemma Phi14 : z ^+ 6 = z ^+ 5 - z ^+ 4 + z ^+ 3 - z ^+ 2 + z - 1.
Proof.
have zN1 : z + 1 != 0.
  apply/eqP => /(congr1 (@complex.Im R)) /=.
  rewrite /= addr0; have := sin_gt_0 t.
  move=> h hs.
  have tpos : Rlt 0 t by rewrite /t; have := PI_RGT_0; lra.
  have tlt : Rlt t PI by rewrite /t; have := PI_RGT_0; lra.
  by have := h tpos tlt; rewrite hs; exact: Rlt_irrefl.
have e : (z + 1) * (z ^+ 6 - z ^+ 5 + z ^+ 4 - z ^+ 3 + z ^+ 2 - z + 1) = 0.
  by have h7 := z7; move: z h7 => w h7; radcan_sym.
move/eqP: e; rewrite mulf_eq0 (negbTE zN1) /= => /eqP hp.
apply/eqP; rewrite -subr_eq0 -[X in _ == X]hp; apply/eqP.
by move: z hp => w _; radcan.
Qed.

(* the identity in C: 2 cos(kt) = z^k + z^-k, then algebra modulo Phi_14 *)
Lemma mainC :
  (E (INR 1 * t) + E (- (INR 1 * t)))
  - (E (INR 2 * t) + E (- (INR 2 * t)))
  + (E (INR 3 * t) + E (- (INR 3 * t))) = 1.
Proof.
rewrite !Ezk !Enk //=.
have h6 := Phi14; move: z h6 => w h6.
radcan_sym.
Qed.

(* back to R: real parts *)
Lemma cos_pi7_mc :
  2 * cos (INR 1 * t) - 2 * cos (INR 2 * t) + 2 * cos (INR 3 * t) = 1.
Proof.
have := mainC; rewrite !ENE -!rmorphB -rmorphD.
by move=> /(congr1 (@complex.Re R)).
Qed.

(* Second part: z is the principal root 7.-root (-1) of mathcomp. This is
   the general lemma E_rootZ of TrigBridge.v, E (PI / n) = n.-root (-1),
   proved once for every n. *)
Lemma z_root : z = 7.-root (-1 : R[i]).
Proof. by rewrite /z /t E_rootZ. Qed.

(* the identity in C again, now by plain radcan on 7.-root (-1): the
   cyclotomic reduction of Tutorial 34 knows Phi_14 *)
Lemma mainC_omega :
  (E (INR 1 * t) + E (- (INR 1 * t)))
  - (E (INR 2 * t) + E (- (INR 2 * t)))
  + (E (INR 3 * t) + E (- (INR 3 * t))) = 1.
Proof. rewrite !Ezk !Enk //= z_root. radcan. Qed.

Local Open Scope R_scope.

Theorem imo1963 : cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
Proof.
have: (2 * cos (INR 1 * t) - 2 * cos (INR 2 * t) + 2 * cos (INR 3 * t) = 1)%R.
  by exact: cos_pi7_mc.
have -> : INR 1 * t = PI / 7 by rewrite /t /=; field.
have -> : INR 2 * t = 2 * PI / 7 by rewrite /t /=; field.
have -> : INR 3 * t = 3 * PI / 7 by rewrite /t /=; field.
lra.
Qed.

(* the same theorem through mainC_omega *)
Theorem imo1963_omega :
  cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
Proof.
have : 2 * cos (INR 1 * t) - 2 * cos (INR 2 * t) + 2 * cos (INR 3 * t) = 1.
  have := mainC_omega; rewrite !ENE -!rmorphB -rmorphD.
  by move=> /(congr1 (@complex.Re R)).
have -> : INR 1 * t = PI / 7 by rewrite /t /=; field.
have -> : INR 2 * t = 2 * PI / 7 by rewrite /t /=; field.
have -> : INR 3 * t = 3 * PI / 7 by rewrite /t /=; field.
lra.
Qed.
