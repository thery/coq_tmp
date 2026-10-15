(******************************************************************************)
(* Independent tests of the polynomial factoring (IrrFactor, MFactor,         *)
(* MFactorEEZ): products of known irreducible factors; each test checks that *)
(* the product of the factors is the input and that their number is right.   *)
(******************************************************************************)

From Stdlib Require Import ZArith.
From mathcomp Require Import all_boot.
From Radcan Require Import IrrFactor MFactor MFactorEEZ.

Local Open Scope Z_scope.

Definition x := mvar 0%N.
Definition y := mvar 1%N.
Definition z := mvar 2%N.
Definition k c := mconst c.
Definition p2 a := mpow a 2%N.
Definition p3 a := mpow a 3%N.

(* ok f n: factoring is exact and gives n factors *)
Definition ok f (n : nat) := mcheck_full f && (size (mfactor_full f) == n)%N.

(* y^2 + c(x) is irreducible when -c(x) is not a square in Z[x] *)

(* (x^2 + y^3 + 1)(y^2 + x^3 + 2): neither factor is linear in any variable *)
Example t1 : ok (mmul (madd (p2 x) (madd (p3 y) (k 1)))
                      (madd (p2 y) (madd (p3 x) (k 2)))) 2%N.
Proof. by vm_compute. Qed.

(* three non-linear factors *)
Example t2 : ok (mmul (madd (p2 x) (madd (p2 y) (k 1)))
                (mmul (madd (p2 x) (madd (mscale 2 (p3 y)) (k 3)))
                      (madd (p2 y) (madd x (k 5))))) 3%N.
Proof. by vm_compute. Qed.

(* three variables *)
Example t3 : ok (mmul (madd (p2 x) (madd (p2 y) (madd (p2 z) (k 1))))
                      (madd (p2 x) (madd (mmul y z) (k 2)))) 2%N.
Proof. by vm_compute. Qed.

(* a non-linear factor times a linear one *)
Example t4 : ok (mmul (madd (p2 x) (madd (p3 y) (k 1))) (msub x y)) 2%N.
Proof. by vm_compute. Qed.

(* irreducible: x^2 + y^5 + 1 *)
Example t5 : ok (madd (p2 x) (madd (mpow y 5) (k 1))) 1%N.
Proof. by vm_compute. Qed.

(* one variable: (x^4 + 1)(x^3 + x + 1)(x^2 - 3) *)
Example t6 : ok (mmul (madd (mpow x 4) (k 1))
                (mmul (madd (p3 x) (madd x (k 1))) (msub (p2 x) (k 3)))) 3%N.
Proof. by vm_compute. Qed.

(* non-constant leading coefficients in both variables:
   (y x^2 + y^3 + 3)(x^3 + x y^2 + y + 1) *)
Example t7 : ok (mmul (madd (mmul y (p2 x)) (madd (p3 y) (k 3)))
                      (madd (p3 x) (madd (mmul x (p2 y)) (madd y (k 1))))) 2%N.
Proof. by vm_compute. Qed.

(* integer content is dropped: 6 (x^2 + y^3 + 1)(x - 2) *)
Example t8 : ok (mscale 6 (mmul (madd (p2 x) (madd (p3 y) (k 1)))
                                (msub x (k 2)))) 2%N.
Proof. by vm_compute. Qed.

(* timings *)
Time Eval vm_compute in ok (mmul (madd (p2 x) (madd (p2 y) (k 1)))
                (mmul (madd (p2 x) (madd (mscale 2 (p3 y)) (k 3)))
                      (madd (p2 y) (madd x (k 5))))) 3%N.
Time Eval vm_compute in ok (mmul (madd (mmul y (p2 x)) (madd (p3 y) (k 3)))
                      (madd (p3 x) (madd (mmul x (p2 y)) (madd y (k 1))))) 2%N.
