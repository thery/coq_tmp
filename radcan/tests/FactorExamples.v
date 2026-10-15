(******************************************************************************)
(* Tests of the polynomial factoring (moved out of IrrFactor.v, MFactor.v and *)
(* MFactorEEZ.v so that the library build does not run them).                *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith.
From mathcomp Require Import all_boot.
From Radcan Require Import IrrFactor MFactor MFactorEEZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* ---- from IrrFactor.v ---- *)

(* Tests (the factors come with a positive leading coefficient) *)

Example uf1 : ufactor [:: -1; 0; 1] = [:: [:: -1; 1]; [:: 1; 1]].
Proof. by vm_compute. Qed.

Example uf2 :
  ufactor [:: -1; 0; 0; 0; 1] = [:: [:: 1; 1]; [:: -1; 1]; [:: 1; 0; 1]].
Proof. by vm_compute. Qed.

Example uf3 : ufactor [:: 4; 0; 0; 0; 1] = [:: [:: 2; 2; 1]; [:: 2; -2; 1]].
Proof. by vm_compute. Qed.

Example uf4 : ufactor [:: -2; 0; 0; 1] = [:: [:: -2; 0; 0; 1]].
Proof. by vm_compute. Qed.

Example uf5 : ufactor [:: -1; 0; 0; 0; 0; 0; 1] =
  [:: [:: -1; 1]; [:: 1; 1; 1]; [:: 1; 1]; [:: 1; -1; 1]].
Proof. by vm_compute. Qed.

Example uf6 : ufactor [:: 1; 0; -10; 0; 1] = [:: [:: 1; 0; -10; 0; 1]].
Proof. by vm_compute. Qed.

Example uf7 : ufactor (zmul [:: 1; 0; 1] [:: 1; 1; 0; 1]) =
  [:: [:: 1; 0; 1]; [:: 1; 1; 0; 1]].
Proof. by vm_compute. Qed.

Example uf8 : ufactor [:: -2; 1; 6] = [:: [:: 2; 3]; [:: -1; 2]].
Proof. by vm_compute. Qed.

(* Swinnerton-Dyer polynomial of sqrt 2, sqrt 3, sqrt 5: irreducible, *)
(* but it splits into linear or quadratic factors modulo every prime   *)
Example uf9 : ufactor [:: 576; 0; -960; 0; 352; 0; -40; 0; 1] =
  [:: [:: 576; 0; -960; 0; 352; 0; -40; 0; 1]].
Proof. by vm_compute. Qed.

Example uf10 : ufactor [:: 2; -4; -6] = [:: [:: -1; 3]; [:: 1; 1]].
Proof. by vm_compute. Qed.

(* ---- from MFactor.v ---- *)

(* Tests: x = variable 0, y = variable 1, z = variable 2, w = variable 3. *)
(* Timings (vm_compute, Rocq 9.1.1) in comments.                         *)

Definition X := mvar 0.
Definition Y := mvar 1.
Definition Z' := mvar 2.
Definition W := mvar 3.
Definition K c := mconst c.

(* Stage 1: homogeneous polynomials *)

(* x^2 - y^2 = (x - y)(x + y), 0.006s *)
Example h1 : mfactor (msub (mpow X 2) (mpow Y 2)) =
  [:: [:: (1, [:: 1%N]); (-1, [:: 0%N; 1%N])];
      [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* x^3 - y^3 = (x - y)(x^2 + x y + y^2), 0.01s *)
Example h2 : mfactor (msub (mpow X 3) (mpow Y 3)) =
  [:: [:: (1, [:: 1%N]); (-1, [:: 0%N; 1%N])];
      [:: (1, [:: 2%N]); (1, [:: 1%N; 1%N]); (1, [:: 0%N; 2%N])]].
Proof. by vm_compute. Qed.

(* x^4 + 4 y^4 = (x^2 - 2 x y + 2 y^2)(x^2 + 2 x y + 2 y^2), 0.008s *)
Example h3 : mfactor (madd (mpow X 4) (mscale 4 (mpow Y 4))) =
  [:: [:: (1, [:: 2%N]); (-2, [:: 1%N; 1%N]); (2, [:: 0%N; 2%N])];
      [:: (1, [:: 2%N]); (2, [:: 1%N; 1%N]); (2, [:: 0%N; 2%N])]].
Proof. by vm_compute. Qed.

(* x^2 + 2 x y + y^2 = (x + y)^2 (not square-free), 0.003s *)
Example h4 : mfactor (mpow (madd X Y) 2) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N])];
      [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* 6 x^2 + x y - 2 y^2 = (3 x + 2 y)(2 x - y), 0.005s *)
Example h5 :
  mfactor (madd (mscale 6 (mpow X 2))
                (msub (mmul X Y) (mscale 2 (mpow Y 2)))) =
  [:: [:: (3, [:: 1%N]); (2, [:: 0%N; 1%N])];
      [:: (2, [:: 1%N]); (-1, [:: 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* x^2 - (y + z)^2 = (x + y + z)(x - y - z), 0.006s *)
Example h6 : mfactor (msub (mpow X 2) (mpow (madd Y Z') 2)) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])];
      [:: (1, [:: 1%N]); (-1, [:: 0%N; 1%N]); (-1, [:: 0%N; 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* x^3 + y^3 + z^3 - 3 x y z, 0.024s *)
Example h7 :
  mfactor (msub (madd (mpow X 3) (madd (mpow Y 3) (mpow Z' 3)))
                (mscale 3 (mmul X (mmul Y Z')))) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])];
      [:: (1, [:: 2%N]); (-1, [:: 1%N; 1%N]); (-1, [:: 1%N; 0%N; 1%N]);
          (1, [:: 0%N; 2%N]); (-1, [:: 0%N; 1%N; 1%N]);
          (1, [:: 0%N; 0%N; 2%N])]].
Proof. by vm_compute. Qed.

(* x^2 (y^4 - z^4): monomial content, then homogeneous, 0.011s *)
Example h8 :
  mcheck (mmul (mpow X 2) (msub (mpow Y 4) (mpow Z' 4))) /\
  size (mfactor (mmul (mpow X 2) (msub (mpow Y 4) (mpow Z' 4)))) = 5%N.
Proof. by vm_compute. Qed.

(* Stage 2: factors of degree <= 1 in some variable *)

(* x y + x + y + 1 = (y + 1)(x + 1), 0.002s *)
Example l1 : mfactor (madd (madd (mmul X Y) X) (madd Y mone)) =
  [:: [:: (1, [:: 0%N; 1%N]); (1, [::])]; [:: (1, [:: 1%N]); (1, [::])]].
Proof. by vm_compute. Qed.

(* x^2 y - y + x^2 - 1 = (y + 1)(x - 1)(x + 1), 0.004s *)
Example l2 :
  mfactor (msub (madd (mmul (mpow X 2) Y) (mpow X 2)) (madd Y mone)) =
  [:: [:: (1, [:: 0%N; 1%N]); (1, [::])]; [:: (1, [:: 1%N]); (-1, [::])];
      [:: (1, [:: 1%N]); (1, [::])]].
Proof. by vm_compute. Qed.

(* x y - 2 x + 3 y - 6 = (y - 2)(x + 3), 0.003s *)
Example l3 :
  mfactor (madd (msub (mmul X Y) (mscale 2 X)) (msub (mscale 3 Y) (K 6))) =
  [:: [:: (1, [:: 0%N; 1%N]); (-2, [::])]; [:: (1, [:: 1%N]); (3, [::])]].
Proof. by vm_compute. Qed.

(* (x^2 + y)(y^2 + x), 0.005s *)
Example l4 : mfactor (mmul (madd (mpow X 2) Y) (madd (mpow Y 2) X)) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 2%N])];
      [:: (1, [:: 2%N]); (1, [:: 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* (x y + z)^2 (x - z), 0.005s *)
Example l5 : mfactor (mmul (mpow (madd (mmul X Y) Z') 2) (msub X Z')) =
  [:: [:: (1, [:: 1%N]); (-1, [:: 0%N; 0%N; 1%N])];
      [:: (1, [:: 1%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])];
      [:: (1, [:: 1%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* (x^2 y + 3 z - 1)(2 x y^2 - z^2 + 5)(x + y + z), 0.11s *)
Example l6 :
  mfactor (mmul (mmul (madd (mmul (mpow X 2) Y) (msub (mscale 3 Z') mone))
                      (madd (mscale 2 (mmul X (mpow Y 2)))
                            (msub (K 5) (mpow Z' 2))))
                (madd X (madd Y Z'))) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])];
      [:: (2, [:: 1%N; 2%N]); (-1, [:: 0%N; 0%N; 2%N]); (5, [::])];
      [:: (1, [:: 2%N; 1%N]); (3, [:: 0%N; 0%N; 1%N]); (-1, [::])]].
Proof. by vm_compute. Qed.

(* (6 x y + 35)(10 x y^2 + 21)(4 x z - 15 y): many divisors, 0.45s *)
Example l7 :
  let f := mmul (mmul (madd (mscale 6 (mmul X Y)) (K 35))
                      (madd (mscale 10 (mmul X (mpow Y 2))) (K 21)))
                (msub (mscale 4 (mmul X Z')) (mscale 15 Y)) in
  mcheck f /\ size (mfactor f) = 3%N.
Proof. by vm_compute. Qed.

(* (x + y + z + 1)^3 (x - 2 y + 3 z), 0.043s *)
Example l8 :
  let f := mmul (mpow (madd X (madd Y (madd Z' mone))) 3)
                (madd (msub X (mscale 2 Y)) (mscale 3 Z')) in
  mcheck f /\ size (mfactor f) = 4%N.
Proof. by vm_compute. Qed.

(* (x w + y z)(x y - z w)(x^2 + y^2 + z^2 + w^2), 0.11s *)
Example l9 :
  let f := mmul (mmul (madd (mmul X W) (mmul Y Z'))
                      (msub (mmul X Y) (mmul Z' W)))
                (madd (mpow X 2) (madd (mpow Y 2)
                                       (madd (mpow Z' 2) (mpow W 2)))) in
  mcheck f /\ size (mfactor f) = 3%N.
Proof. by vm_compute. Qed.

(* Out of reach of stages 1-2 (no factor of degree <= 1 in any variable): *)
(* (210 x^2 + y^3 + 1)(x^2 + 2 y^2 + 11) is returned unsplit, 0.13s      *)
Example f1 :
  let f := mmul (madd (mscale 210 (mpow X 2)) (madd (mpow Y 3) mone))
                (madd (mpow X 2) (madd (mscale 2 (mpow Y 2)) (K 11))) in
  mfactor f = [:: f].
Proof. by vm_compute. Qed.

(* Degenerate inputs: constants, monomials, univariate, sign and content *)
Example d1 :
  [seq mfactor f | f <- [:: K 6; X; mmul (mpow X 2) Y]] =
  [:: [::]; [:: X]; [:: X; X; Y]] /\
  mfactor (mmul (mpow (msub X mone) 2) (madd X (K 2))) =
    [:: msub X mone; msub X mone; madd X (K 2)] /\
  mfactor (mscale (-3) (msub Y (mpow X 2))) = [:: msub (mpow X 2) Y].
Proof. by vm_compute. Qed.

(* ---- from MFactorEEZ.v ---- *)

(* Tests: x = X, y = Y, z = Z', w = W (from MFactor).  Timings (vm_compute, *)
(* Rocq 9.1.1) in comments.                                                *)

(* (210 x^2 + y^3 + 1)(x^2 + 2 y^2 + 11), unsplit by stages 1-2, 0.12s *)
Example e1 :
  let f := mmul (madd (mscale 210 (mpow X 2)) (madd (mpow Y 3) mone))
                (madd (mpow X 2) (madd (mscale 2 (mpow Y 2)) (K 11))) in
  mfactor_full f =
  [:: [:: (1, [:: 2%N]); (2, [:: 0%N; 2%N]); (11, [::])];
      [:: (210, [:: 2%N]); (1, [:: 0%N; 3%N]); (1, [::])]].
Proof. by vm_compute. Qed.

(* (x^2 + y^2 + 1)(x^2 - y^2 + 2 x y + 3), 0.04s *)
Example e2 :
  mfactor_full (mmul (madd (mpow X 2) (madd (mpow Y 2) mone))
                     (madd (msub (mpow X 2) (mpow Y 2))
                           (madd (mscale 2 (mmul X Y)) (K 3)))) =
  [:: [:: (1, [:: 2%N]); (2, [:: 1%N; 1%N]); (-1, [:: 0%N; 2%N]);
          (3, [::])];
      [:: (1, [:: 2%N]); (1, [:: 0%N; 2%N]); (1, [::])]].
Proof. by vm_compute. Qed.

(* (x^3 + y^2 z + 1)(x z^2 + y^3 - 2): already split by stage 2, 0.03s *)
Example e3 :
  let f := mmul (madd (mpow X 3) (madd (mmul (mpow Y 2) Z') mone))
                (madd (mmul X (mpow Z' 2)) (msub (mpow Y 3) (K 2))) in
  mfactor_full f = mfactor f /\ size (mfactor f) = 2%N.
Proof. by vm_compute. Qed.

(* x^2 - y^4 + y^2 - 1 is irreducible but its images at y = 0, 1, -1 *)
(* split into two factors: the lifting fails, 0.03s                  *)
Definition SD := msub (mpow X 2) (madd (mpow Y 4) (msub mone (mpow Y 2))).

Example e4 : mfactor_full SD = [:: SD].
Proof. by vm_compute. Qed.

(* recombination: 3 image factors, 2 true factors, 0.1s *)
Example e5 :
  mfactor_full (mmul SD (madd (mpow X 2) (madd (mpow Y 2) mone))) =
  [:: madd (mpow X 2) (madd (mpow Y 2) mone); SD].
Proof. by vm_compute. Qed.

(* irreducible, 0.003s *)
Example e6 : mfactor_full (madd (mpow X 2) (madd (mpow Y 2) mone)) =
  [:: madd (mpow X 2) (madd (mpow Y 2) mone)].
Proof. by vm_compute. Qed.

(* non-constant leading coefficients in every variable:          *)
(* ((y^2 + 1) x^2 + y^3 x + 2)((y + 2) x^2 + y^2 + 3), 0.28s      *)
Example e7 :
  let g1 := madd (mmul (madd (mpow Y 2) mone) (mpow X 2))
                 (madd (mmul (mpow Y 3) X) (K 2)) in
  let g2 := madd (mmul (madd Y (K 2)) (mpow X 2)) (madd (mpow Y 2) (K 3)) in
  mfactor (mmul g1 g2) = [:: mmul g1 g2] /\
  mfactor_full (mmul g1 g2) = [:: g1; g2].
Proof. by vm_compute. Qed.

(* the image at y = 0 is not square-free: shifted point, 0.07s *)
Example e8 :
  let s1 := madd (mpow X 2) (madd (mpow Y 2) Y) in
  let s2 := madd (msub (mpow X 2) (mpow Y 2))
                 (madd (mscale 3 Y) (madd (mmul X Y) mone)) in
  mfactor_full (mmul s1 s2) = [:: s1; s2].
Proof. by vm_compute. Qed.

(* three variables, three factors, 1.1s *)
Example e9 :
  let k1 :=
    madd (mpow X 2) (madd (mmul (mpow Y 2) Z') (madd (mpow Z' 2) mone)) in
  let k2 := madd (mmul (mpow X 2) (mpow Z' 2))
                 (madd (mmul (mpow Y 2) X) (msub (K 5) (mpow Z' 2))) in
  let f := mmul (mmul k1 k2) (madd (mpow X 2) (madd (mpow Y 2) (mpow Z' 2))) in
  mcheck_full f /\ size (mfactor_full f) = 3%N.
Proof. by vm_compute. Qed.

(* non-constant leading coefficient, three variables, 0.4s *)
Example e10 :
  let r1 := madd (mmul (mpow X 2) (madd Y Z'))
                 (madd (mmul (mpow Y 2) Z') (madd (mpow Z' 2) mone)) in
  let r2 := madd (mmul (mpow X 2) (mpow Z' 2))
                 (madd (mmul (mpow Y 2) X) (msub (mmul Y Z') (K 2))) in
  mfactor (mmul r1 r2) = [:: mmul r1 r2] /\
  mcheck_full (mmul r1 r2) /\ size (mfactor_full (mmul r1 r2)) = 2%N.
Proof. by vm_compute. Qed.

(* not square-free: returned unsplit (limitation), 0.007s *)
Example e11 :
  let f := mpow (madd (mpow X 2) (madd (mpow Y 2) mone)) 2 in
  mfactor_full f = [:: f].
Proof. by vm_compute. Qed.

(* stages 1-2 results are unchanged (inputs of MFactor's tests), 0.6s *)
Example e12 :
  let fs := [:: msub (mpow X 2) (mpow Y 2); msub (mpow X 3) (mpow Y 3);
    madd (mpow X 4) (mscale 4 (mpow Y 4)); mpow (madd X Y) 2;
    msub (mpow X 2) (mpow (madd Y Z') 2);
    msub (madd (mpow X 3) (madd (mpow Y 3) (mpow Z' 3)))
         (mscale 3 (mmul X (mmul Y Z')));
    mmul (mpow X 2) (msub (mpow Y 4) (mpow Z' 4));
    madd (madd (mmul X Y) X) (madd Y mone);
    msub (madd (mmul (mpow X 2) Y) (mpow X 2)) (madd Y mone);
    mmul (madd (mpow X 2) Y) (madd (mpow Y 2) X);
    mmul (mpow (madd (mmul X Y) Z') 2) (msub X Z');
    mmul (mmul (madd (mmul (mpow X 2) Y) (msub (mscale 3 Z') mone))
               (madd (mscale 2 (mmul X (mpow Y 2))) (msub (K 5) (mpow Z' 2))))
         (madd X (madd Y Z'));
    mmul (mmul (madd (mscale 6 (mmul X Y)) (K 35))
               (madd (mscale 10 (mmul X (mpow Y 2))) (K 21)))
         (msub (mscale 4 (mmul X Z')) (mscale 15 Y));
    mmul (mmul (madd (mmul X W) (mmul Y Z')) (msub (mmul X Y) (mmul Z' W)))
         (madd (mpow X 2) (madd (mpow Y 2) (madd (mpow Z' 2) (mpow W 2))));
    K 6; X; mscale (-3) (msub Y (mpow X 2))] in
  all (fun f => all2 meqb (mfactor_full f) (mfactor f)) fs.
Proof. by vm_compute. Qed.

