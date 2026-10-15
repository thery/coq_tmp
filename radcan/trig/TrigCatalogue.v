(******************************************************************************)
(* TrigCatalogue: standard trigonometric identities, each proved by one call *)
(* of radcan_trig (the conditions it returns are closed from the hypotheses  *)
(* by radcan_trig itself).  Identities with variables first, then special    *)
(* values.  The identities out of reach are listed in the last section, in   *)
(* a comment, with the reason.                                               *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From RadcanTrig Require Import TrigTac.

Local Open Scope R_scope.

(* Pythagorean *)
Lemma c_pyth x : sin x ^ 2 + cos x ^ 2 = 1.
Proof. radcan_trig. Qed.
Lemma c_sec x : cos x <> 0 -> 1 + tan x ^ 2 = 1 / cos x ^ 2.
Proof. intros h. radcan_trig. Qed.
(* parity *)
Lemma c_cosN x : cos (- x) = cos x.
Proof. radcan_trig. Qed.
Lemma c_sinN x : sin (- x) = - sin x.
Proof. radcan_trig. Qed.
Lemma c_tanN x : cos x <> 0 -> tan (- x) = - tan x.
Proof. intros h. radcan_trig. Qed.
(* shifts *)
Lemma c_cosPI2 x : cos (x + PI / 2) = - sin x.
Proof. radcan_trig. Qed.
Lemma c_sinPI2 x : sin (x + PI / 2) = cos x.
Proof. radcan_trig. Qed.
Lemma c_sinPIm x : sin (PI - x) = sin x.
Proof. radcan_trig. Qed.
Lemma c_cosPIm x : cos (PI - x) = - cos x.
Proof. radcan_trig. Qed.
Lemma c_cosPI x : cos (x + PI) = - cos x.
Proof. radcan_trig. Qed.
Lemma c_tanPI x : cos x <> 0 -> tan (x + PI) = tan x.
Proof. intros h. radcan_trig. Qed.
Lemma c_cos2PI x : cos (x + 2 * PI) = cos x.
Proof. radcan_trig. Qed.
(* addition / subtraction *)
Lemma c_cosD x y : cos (x + y) = cos x * cos y - sin x * sin y.
Proof. radcan_trig. Qed.
Lemma c_cosB x y : cos (x - y) = cos x * cos y + sin x * sin y.
Proof. radcan_trig. Qed.
Lemma c_sinD x y : sin (x + y) = sin x * cos y + cos x * sin y.
Proof. radcan_trig. Qed.
Lemma c_sinB x y : sin (x - y) = sin x * cos y - cos x * sin y.
Proof. radcan_trig. Qed.
Lemma c_tanD x y : cos x <> 0 -> cos y <> 0 -> cos (x + y) <> 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof. intros hx hy hxy. radcan_trig. Qed.
Lemma c_tanB x y : cos x <> 0 -> cos y <> 0 -> cos (x - y) <> 0 ->
  tan (x - y) = (tan x - tan y) / (1 + tan x * tan y).
Proof. intros hx hy hxy. radcan_trig. Qed.
(* double and triple angle *)
Lemma c_sin2 x : sin (2 * x) = 2 * sin x * cos x.
Proof. radcan_trig. Qed.
Lemma c_cos2 x : cos (2 * x) = cos x ^ 2 - sin x ^ 2.
Proof. radcan_trig. Qed.
Lemma c_cos2c x : cos (2 * x) = 2 * cos x ^ 2 - 1.
Proof. radcan_trig. Qed.
Lemma c_cos2s x : cos (2 * x) = 1 - 2 * sin x ^ 2.
Proof. radcan_trig. Qed.
Lemma c_tan2 x : cos x <> 0 -> cos (2 * x) <> 0 ->
  tan (2 * x) = 2 * tan x / (1 - tan x ^ 2).
Proof. intros h h2. radcan_trig. Qed.
Lemma c_sin3 x : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3.
Proof. radcan_trig. Qed.
Lemma c_cos3 x : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x.
Proof. radcan_trig. Qed.
Lemma c_tan3 x : cos x <> 0 -> cos (3 * x) <> 0 ->
  tan (3 * x) = (3 * tan x - tan x ^ 3) / (1 - 3 * tan x ^ 2).
Proof. intros h h3. radcan_trig. Qed.
(* half angle, polynomial form *)
Lemma c_half_cos y : cos y ^ 2 = (1 + cos (2 * y)) / 2.
Proof. radcan_trig. Qed.
Lemma c_half_sin y : sin y ^ 2 = (1 - cos (2 * y)) / 2.
Proof. radcan_trig. Qed.
Lemma c_half_tan y : cos y <> 0 -> sin (2 * y) <> 0 ->
  tan y = (1 - cos (2 * y)) / sin (2 * y).
Proof. intros h h2. radcan_trig. Qed.
(* power reduction *)
Lemma c_sin3r x : sin x ^ 3 = (3 * sin x - sin (3 * x)) / 4.
Proof. radcan_trig. Qed.
Lemma c_cos3r x : cos x ^ 3 = (3 * cos x + cos (3 * x)) / 4.
Proof. radcan_trig. Qed.
Lemma c_cos4r x : cos x ^ 4 = (3 + 4 * cos (2 * x) + cos (4 * x)) / 8.
Proof. radcan_trig. Qed.
(* product-to-sum *)
Lemma c_pcc x y : cos x * cos y = (cos (x - y) + cos (x + y)) / 2.
Proof. radcan_trig. Qed.
Lemma c_pss x y : sin x * sin y = (cos (x - y) - cos (x + y)) / 2.
Proof. radcan_trig. Qed.
Lemma c_psc x y : sin x * cos y = (sin (x + y) + sin (x - y)) / 2.
Proof. radcan_trig. Qed.
(* sum-to-product, with x = a + b, y = a - b *)
Lemma c_scc a b : cos (a + b) + cos (a - b) = 2 * cos a * cos b.
Proof. radcan_trig. Qed.
Lemma c_scc' a b : cos (a + b) - cos (a - b) = - 2 * sin a * sin b.
Proof. radcan_trig. Qed.
Lemma c_sss a b : sin (a + b) + sin (a - b) = 2 * sin a * cos b.
Proof. radcan_trig. Qed.
Lemma c_cdiff x y : cos (x + y) * cos (x - y) = cos x ^ 2 - sin y ^ 2.
Proof. radcan_trig. Qed.
(* Chebyshev *)
Lemma c_cheb4 x : cos (4 * x) = 8 * cos x ^ 4 - 8 * cos x ^ 2 + 1.
Proof. radcan_trig. Qed.
Lemma c_cheb5 x : cos (5 * x) = 16 * cos x ^ 5 - 20 * cos x ^ 3 + 5 * cos x.
Proof. radcan_trig. Qed.
Lemma c_sin5 x : sin (5 * x) = 16 * sin x ^ 5 - 20 * sin x ^ 3 + 5 * sin x.
Proof. radcan_trig. Qed.
(* telescoping product *)
Lemma c_prod x : sin x <> 0 ->
  cos x * cos (2 * x) * cos (4 * x) = sin (8 * x) / (8 * sin x).
Proof. intros h. radcan_trig. Qed.
(* three variables *)
Lemma c_sin3v x y z : sin (x + y + z) = sin x * cos y * cos z
  + cos x * sin y * cos z + cos x * cos y * sin z - sin x * sin y * sin z.
Proof. radcan_trig. Qed.
Lemma c_mix x y :
  cos (2 * x - y) = cos (2 * x) * cos y + sin (2 * x) * sin y.
Proof. radcan_trig. Qed.
(* larger multiples and three angles *)
Lemma c_cheb7 x : cos (7 * x) =
  64 * cos x ^ 7 - 112 * cos x ^ 5 + 56 * cos x ^ 3 - 7 * cos x.
Proof. radcan_trig. Qed.
Lemma c_cheb10 x : cos (10 * x) = 512 * cos x ^ 10 - 1280 * cos x ^ 8
  + 1120 * cos x ^ 6 - 400 * cos x ^ 4 + 50 * cos x ^ 2 - 1.
Proof. radcan_trig. Qed.
Lemma c_tan3v x y z : cos x <> 0 -> cos y <> 0 -> cos z <> 0 ->
  cos (x + y + z) <> 0 ->
  tan (x + y + z) = (tan x + tan y + tan z - tan x * tan y * tan z)
    / (1 - tan x * tan y - tan y * tan z - tan z * tan x).
Proof. intros. radcan_trig. Qed.
(* any angle is an atom: here x ^ 2 *)
Lemma c_atom x : cos (x ^ 2) ^ 2 + sin (x ^ 2) ^ 2 = 1.
Proof. radcan_trig. Qed.

(* special values *)
Lemma v_sin6 : sin (PI / 6) = 1 / 2.
Proof. radcan_trig. Qed.
Lemma v_cos6 : cos (PI / 6) = sqrt 3 / 2.
Proof. radcan_trig. Qed.
Lemma v_tan6 : tan (PI / 6) = sqrt 3 / 3.
Proof. radcan_trig. Qed.
Lemma v_cos4 : cos (PI / 4) = sqrt 2 / 2.
Proof. radcan_trig. Qed.
Lemma v_sin4 : sin (PI / 4) = sqrt 2 / 2.
Proof. radcan_trig. Qed.
Lemma v_tan4 : tan (PI / 4) = 1.
Proof. radcan_trig. Qed.
Lemma v_cos3 : cos (PI / 3) = 1 / 2.
Proof. radcan_trig. Qed.
Lemma v_sin3 : sin (PI / 3) = sqrt 3 / 2.
Proof. radcan_trig. Qed.
Lemma v_tan3 : tan (PI / 3) = sqrt 3.
Proof. radcan_trig. Qed.
Lemma v_cos2 : cos (PI / 2) = 0.
Proof. radcan_trig. Qed.
Lemma v_sin2 : sin (PI / 2) = 1.
Proof. radcan_trig. Qed.
Lemma v_cosPI : cos PI = -1.
Proof. radcan_trig. Qed.
Lemma v_sinPI : sin PI = 0.
Proof. radcan_trig. Qed.
Lemma v_tanPI : tan PI = 0.
Proof. radcan_trig. Qed.
Lemma v_cos23 : cos (2 * PI / 3) = - 1 / 2.
Proof. radcan_trig. Qed.
Lemma v_sin23 : sin (2 * PI / 3) = sqrt 3 / 2.
Proof. radcan_trig. Qed.
Lemma v_cos5 : cos (PI / 5) = (1 + sqrt 5) / 4.
Proof. radcan_trig. Qed.
Lemma v_cos25 : cos (2 * PI / 5) = (sqrt 5 - 1) / 4.
Proof. radcan_trig. Qed.
Lemma v_sin5sq : sin (PI / 5) ^ 2 = (5 - sqrt 5) / 8.
Proof. radcan_trig. Qed.
Lemma v_cos8sq : cos (PI / 8) ^ 2 = (2 + sqrt 2) / 4.
Proof. radcan_trig. Qed.
Lemma v_cos12 : cos (PI / 12) = (sqrt 6 + sqrt 2) / 4.
Proof. radcan_trig. Qed.
Lemma v_sin12 : sin (PI / 12) = (sqrt 6 - sqrt 2) / 4.
Proof. radcan_trig. Qed.
Lemma v_tan12 : tan (PI / 12) = 2 - sqrt 3.
Proof. radcan_trig. Qed.
Lemma v_imo :
  cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
Proof. radcan_trig. Qed.
Lemma v_sum5 : cos (2 * PI / 5) + cos (4 * PI / 5) = - 1 / 2.
Proof. radcan_trig. Qed.
Lemma v_prod7 :
  cos (PI / 7) * cos (2 * PI / 7) * cos (3 * PI / 7) = 1 / 8.
Proof. radcan_trig. Qed.
Lemma v_sin18 : 8 * sin (PI / 18) ^ 3 - 6 * sin (PI / 18) + 1 = 0.
Proof. radcan_trig. Qed.
Lemma v_cos9 :
  cos (PI / 9) * cos (2 * PI / 9) * cos (4 * PI / 9) = 1 / 8.
Proof. radcan_trig. Qed.
Lemma v_shift x :
  sin (x + PI / 7) = sin x * cos (PI / 7) + cos x * sin (PI / 7).
Proof. radcan_trig. Qed.
Lemma v_shift12 x : cos (x + PI / 12) =
  cos x * (sqrt 6 + sqrt 2) / 4 - sin x * (sqrt 6 - sqrt 2) / 4.
Proof. radcan_trig. Qed.
Lemma v_sin15 : sin (PI / 15) * sin (2 * PI / 15) * sin (4 * PI / 15)
  * sin (7 * PI / 15) = 1 / 16.
Proof. radcan_trig. Qed.
Lemma v_gauss7 :
  sin (2 * PI / 7) + sin (4 * PI / 7) - sin (6 * PI / 7) = sqrt 7 / 2.
Proof. radcan_trig. Qed.

(* refused: identities that are false *)
Lemma f_cos2 x : cos (2 * x) = 2 * cos x - 1.
Proof. Fail radcan_trig. Abort.
Lemma f_cos5 : cos (PI / 5) = 1 / 2.
Proof. Fail radcan_trig. Abort.

(* conditions returned when the hypotheses are missing: here cos x <> 0,
   cos x ^ 2 - sin x ^ 2 <> 0 and cos (2 * x) <> 0 are left to the user *)
Lemma l_tan2 x : tan (2 * x) = 2 * tan x / (1 - tan x ^ 2).
Proof. radcan_trig. Abort.

(* Out of reach (no Lemma, the reason in plain words):
   - cos (PI / 8) = sqrt (2 + sqrt 2) / 2 : a square root of a square root;
     only square roots of numerals are translated (cos (PI / 8) ^ 2 =
     (2 + sqrt 2) / 4, v_cos8sq above, is proved)
   - cos x = 2 * cos (x / 2) ^ 2 - 1 : x / 2 is not an integer multiple of
     a variable; write the identity with x = 2 * y (c_cos2c above)
   - sin x = 1 -> cos x = 0 : hypotheses that are equations are not used
   - sqrt (1 - sin x ^ 2) = Rabs (cos x) : square root of a non-numeral
     and absolute value
   - sin (PI / 18) = (a closed form) : no expression with real square or
     cube roots exists; its cubic equation (v_sin18 above) is proved
   - inequalities (Rabs (sin x) <= 1), arcsin, arctan, exp, ln: out of the
     scope of the tactic *)
