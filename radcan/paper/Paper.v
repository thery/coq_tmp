(******************************************************************************)
(* Paper: the examples of Caviness & Fateman, Simplification of Radical       *)
(* Expressions (radcan.md).                                                   *)
(* Proved: section 2 (phase 3, form 1, form 2, the nested example), (1) as   *)
(* an identity and as a quotient, (8), (3) with the corrected E, the          *)
(* rationalisation of D, and (4) = (6) on C with omega = 3.-root (-1).        *)
(* Refused because false: (3) as printed, E with the printed 54 x (the right  *)
(* coefficient is 108 x).  The misprint in (3) is x^5 for x^6 in the          *)
(* denominator: with x^6, (3) is proved with its printed numerator (eq3p).    *)
(* (2): false for mathcomp's principal roots in its first reading; proved in *)
(* its second reading (values of omega_4) and in the paper's own symbolic    *)
(* reading (roots given by hypotheses, radcan_sym, under x != 1).            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR Syntax Radcan.
From Radcan Require Import Refine Tactic OddRoot NegRootC Sym SymTac.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Paper.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* (1): x - y over sqrt x + sqrt y is sqrt x - sqrt y *)
Lemma eq1 : 0 <= x -> 0 <= y ->
  x - y = (\sqrt x - \sqrt y) * (\sqrt x + \sqrt y).
Proof. move=> hx hy. radcan. all: by []. Qed.
(* as a quotient: the denominator is rationalised (M11) *)
Lemma eq1q : 0 <= x -> 0 <= y -> x != y ->
  (x - y) / (\sqrt x + \sqrt y) = \sqrt x - \sqrt y.
Proof. move=> hx hy hxy. radcan. all: by []. Qed.

(* §2, phase 3: (2^(1/6))^7 = 2 * 2^(1/6) *)
Lemma phase3 : 6.-proot 2 ^+ 7 = 2 * 6.-proot 2.
Proof. radcan. Qed.

(* §2, form 2: square-free factorisation of the radicand *)
Lemma form2 : -3 <= x -> -2 <= 3 * x + x ^+ 2 ->
  \sqrt (x ^+ 4 + 9 * x ^+ 3 + 29 * x ^+ 2 + 39 * x + 18) =
  (x + 3) * \sqrt (x ^+ 2 + 3 * x + 2).
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* §2: with (x+2)^(1/3) the basis splits x^2 + 3x + 2 = (x+1)(x+2) and
   (x+2)^(1/2), (x+2)^(1/3) are merged over index 6 *)
Lemma form1 : -1 <= x ->
  \sqrt (x ^+ 4 + 9 * x ^+ 3 + 29 * x ^+ 2 + 39 * x + 18) + 3.-proot (x + 2)
  = (x + 3) * \sqrt (x + 1) * 6.-proot ((x + 2) ^+ 3) +
    6.-proot ((x + 2) ^+ 2).
Proof. move=> h. radcan. exact: h. Qed.

(* the nested example of §2 (M13): the inner radicand is normalised first;
   raw: 0 <= x + 1, 0 <= x + 2   refined: -1 <= x *)
Lemma nested : -1 <= x ->
  \sqrt (x ^+ 2 + 3 * x + 3 + \sqrt (x + 1) * \sqrt (x + 1)) = x + 2.
Proof. move=> h. radcan. exact: h. Qed.

(* (3) as printed is FALSE (check at x = 5/2): radcan refuses it; the
   denominator should start with x ^+ 6, not x ^+ 5 (see eq3p) *)
Goal (x + \sqrt 2 + 3.-proot 9) *
  ((((2 * x ^+ 3 - 4 * x - 9) * \sqrt 2 - x ^+ 4 - 9 * x + 4) * 3.-proot 9)
  + (((-9) * x ^+ 2 - 6) * \sqrt 2 + 3 * x ^+ 3 + 18 * x + 27) * 3.-proot 3
  + ((- x ^+ 4 + 4 * x ^+ 2 + 18 * x - 4) * \sqrt 2 + x ^+ 5 - 4 * x ^+ 3
     + 9 * x ^+ 2 + 4 * x + 18))
  = x ^+ 5 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73.
Proof. Fail radcan. Abort.

(* (8): 1 / (x + sqrt 2 + 3^(2/3)) = N / D with D = (x + sqrt 2)^3 + 9 *)
Lemma eq8 : (x + \sqrt 2 + 3.-proot 9) *
  (- (x + \sqrt 2) * 3.-proot 9 + 3 * 3.-proot 3
   + (x ^+ 2 + 2 * \sqrt 2 * x + 2))
  = (x + \sqrt 2) ^+ 3 + 9.
Proof. radcan. Qed.

(* end of §2: D times its conjugate is E; the paper prints 54 x, which is
   refused, the right coefficient is 108 x *)
Goal ((x + \sqrt 2) ^+ 3 + 9) *
     (x ^+ 3 + 6 * x + 9 - (3 * x ^+ 2 + 2) * \sqrt 2)
   = x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 54 * x + 73.
Proof. Fail radcan. Abort.
(* (3) with the corrected E, as a quotient: 1 / d = N8 * conj / E *)
Lemma eq3 :
  x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73 != 0 ->
  1 / (x + \sqrt 2 + 3.-proot 9) =
  (- (x + \sqrt 2) * 3.-proot 9 + 3 * 3.-proot 3
     + (x ^+ 2 + 2 * \sqrt 2 * x + 2))
  * (x ^+ 3 + 6 * x + 9 - (3 * x ^+ 2 + 2) * \sqrt 2)
  / (x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73).
Proof.
move=> hE. radcan_raw.
by apply: contra_neq hE => h; rewrite -h; radcan.
Qed.

(* (3) as printed, with x ^+ 6 in place of the misprinted x ^+ 5: the
   printed numerator is right *)
Lemma eq3p :
  x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73 != 0 ->
  1 / (x + \sqrt 2 + 3.-proot 9) =
  ((((2 * x ^+ 3 - 4 * x - 9) * \sqrt 2 - x ^+ 4 - 9 * x + 4) * 3.-proot 9)
  + (((-9) * x ^+ 2 - 6) * \sqrt 2 + 3 * x ^+ 3 + 18 * x + 27) * 3.-proot 3
  + ((- x ^+ 4 + 4 * x ^+ 2 + 18 * x - 4) * \sqrt 2 + x ^+ 5 - 4 * x ^+ 3
     + 9 * x ^+ 2 + 4 * x + 18))
  / (x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73).
Proof.
move=> hE. radcan_raw.
by apply: contra_neq hE => h; rewrite -h; radcan.
Qed.

Lemma eqE : ((x + \sqrt 2) ^+ 3 + 9) *
           (x ^+ 3 + 6 * x + 9 - (3 * x ^+ 2 + 2) * \sqrt 2)
   = x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73.
Proof. radcan. Qed.
End Paper.

Section PaperC.
Variables (C : numClosedFieldType) (x : C).
(* (2): with mathcomp's principal roots the left side is - sqrt 2, not 0;
   the paper's convention (1-x)^(3/4) = ((1-x)^(1/4))^3 gives 0 but needs
   the cyclotomic relation of omega_8, not used by radcan *)
Goal 4.-root (x - 1) / 4.-root (1 - x)
     - 4.-root ((x - 1) ^+ 3) / 4.-root ((1 - x) ^+ 3) - 2.-root 2 = 0.
Proof. Fail radcan. Abort.
(* the second reading: omega_rw in radcan's pre-pass (Tutorial 29); the
   plain check also proves it since the Gauss-sum mode (Tutorial 37):
   sqrt 2 = omega_4 - omega_4 ^+ 3, same condition 1 < x *)
Goal 1 < x -> 4.-root (x - 1) / 4.-root (1 - x)
     - 4.-root (x - 1) ^+ 3 / 4.-root (1 - x) ^+ 3 - 2.-root 2 = 0.
Proof. move=> h. radcan_plain_gen true. exact: h. Qed.
(* (4) = (6), with omega = 3.-root (-1) (= omega_6 ^+ 2 in the paper's
   convention omega_m = e^(i pi / m); the printed omega_6 makes it false);
   raw: 0 <= x ^+ 2 + 1   refined: -1 <= x ^+ 2 *)
Lemma eq46 : -1 <= x ^+ 2 ->
  (4.-root 2 + 2.-root 3 * 3.-root (- (x ^+ 2 + 1))) / 2.-root (x ^+ 2 + 1) =
  1 / (x ^+ 2 + 1) * 4.-root 2 * 6.-root (x ^+ 2 + 1) ^+ 3 +
  1 / (x ^+ 2 + 1) * 3.-root (-1) * 2.-root 3 * 6.-root (x ^+ 2 + 1) ^+ 5.
Proof. move=> h. radcan. exact: h. Qed.
End PaperC.

(* (2) in the paper's own reading, with roots given by hypotheses (M15) *)
(* The paper's (2): (x-1)^(1/4) / (1-x)^(1/4) - (x-1)^(3/4) / (1-x)^(3/4)
   - sqrt 2 = 0.  Its reading: u = (x-1)^(1/4), (1-x)^(1/4) = w u with
   w = (-1)^(1/4), (x-1)^(3/4) = u^3, (1-x)^(3/4) = (w u)^3, and sqrt 2 the
   element w - w^3 of the extension (sym6).  The cancellation u / u needs
   u != 0, i.e. x != 1, which the paper leaves implicit (for x = 1 the left
   side is - sqrt 2). *)
Section PaperSym.
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
End PaperSym.
