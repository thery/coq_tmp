(******************************************************************************)
(* Tutorial 39: explog, exponentials and logarithms on the reals of Stdlib,  *)
(* following the Structure Theorem of Epstein-Caviness (TR223, Thm 5.7).     *)
(* Needs explog/ built (cd explog && rocq makefile -f _CoqProject -o         *)
(* Makefile && make), after rocq/ and trig/.                                  *)
(******************************************************************************)

From RadcanExpLog Require Import ExpLogTac.
Local Open Scope R_scope.

(* exp pass: the arguments x/2, x/3, x/6 are related over Q (Gaussian
   elimination); the letter is exp (x / 6) *)
Lemma e1 x : exp (x / 2) * exp (x / 3) * exp (x / 6) = exp x.
Proof. explog. Qed.

(* a relation hidden by denominators: x/(x+1) + 1/(x+1) = 1, checked by
   field under x + 1 <> 0 *)
Lemma e2 x : x + 1 <> 0 -> exp (x / (x + 1)) * exp (1 / (x + 1)) = exp 1.
Proof. move=> h. explog. Qed.

(* ln letters inside exp: exp (3 ln x) = x ^ 3, under 0 < x *)
Lemma e3 x : 0 < x -> exp (2 * x + 3 * ln x) = x ^ 3 * exp x ^ 2.
Proof. move=> h. explog. Qed.

(* ln pass: the argument is factored; ln |A| splits under p <> 0 only *)
Lemma l1 x : 1 < x -> ln (x ^ 2 - 1) - ln (x - 1) - ln (x + 1) = 0.
Proof. move=> h. explog. Qed.

Lemma l2 x : x <> 0 -> ln (x ^ 2) = 2 * ln (Rabs x).
Proof. move=> h. explog. Qed.

(* constants: integer factoring only *)
Lemma l3 : ln 12 - ln 3 = 2 * ln 2.
Proof. explog. Qed.

(* unfolded functions and trigonometry (the zero test is radcan_trig) *)
Lemma h1 x y : tanh (x + y) = (tanh x + tanh y) / (1 + tanh x * tanh y).
Proof. explog. Qed.

Lemma t1 x : exp x * sin (2 * x) = 2 * exp x * sin x * cos x.
Proof. explog. Qed.

(* without hypothesis the conditions are given back as goals *)
Goal forall x, exp (2 * x + 3 * ln x) = x ^ 3 * exp x ^ 2.
Proof. move=> x. explog. (* 0 < x *) Abort.

(* false goals and relations between constants fail *)
Goal ln 2 + ln 3 = ln 5.
Proof. Fail explog. Abort.
