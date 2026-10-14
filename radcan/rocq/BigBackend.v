(******************************************************************************)
(* BigBackend: the Bignums number backend BigNum : NUM, int = BigZ and        *)
(* rat = BigQ (machine integers, fast on large numbers under vm_compute).     *)
(* The specification comes from the BigZ.spec_* and BigQ.spec_* lemmas.       *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith QArith_base.
From Stdlib Require Import Qreduction.
From Bignums Require Import BigZ BigQ.
From mathcomp Require Import ssreflect ssrbool.
From Radcan Require Import Backend.

Module BigNum <: NUM.

Definition int := bigZ.
Definition rat := bigQ.
Definition i_to_Z (a : int) : Z := BigZ.to_Z a.
Definition i_of_Z (z : Z) : int := BigZ.of_Z z.
Definition c_to_Q (a : rat) : Q := BigQ.to_Q a.

Definition i_zero : int := BigZ.zero.
Definition i_one : int := BigZ.one.
Definition i_add (a b : int) : int := BigZ.add a b.
Definition i_mul (a b : int) : int := BigZ.mul a b.
Definition i_pow (b : positive) (k : nat) : int :=
  BigZ.pow (BigZ.of_Z (Zpos b)) (BigZ.of_Z (Z.of_nat k)).
Definition i_eqb (a b : int) : bool := BigZ.eqb a b.
Definition i_ltb (a b : int) : bool := BigZ.ltb a b.
Definition i_rem (a b : int) : int := BigZ.rem a b.
Definition i_div (a b : int) : int := BigZ.div a b.
Definition i_gcd (a b : int) : int := BigZ.gcd a b.
Definition i_succ (a : int) : int := BigZ.succ a.
Definition i_sqrt (a : int) : int := BigZ.sqrt a.
Definition i_to_pos (a : int) : positive := Z.to_pos (BigZ.to_Z a).
Definition i_to_nat (a : int) : nat := Z.to_nat (BigZ.to_Z a).
Definition i_size (a : int) : nat := S (Z.to_nat (BigZ.to_Z (BigZ.log2 a))).

Definition c_zero : rat := BigQ.zero.
Definition c_one : rat := BigQ.one.
Definition c_of_int (a : int) : rat := BigQ.Qz a.
Definition c_of_Z (z : Z) : rat := BigQ.Qz (BigZ.of_Z z).
Definition c_add (a b : rat) : rat := BigQ.add_norm a b.
Definition c_sub (a b : rat) : rat := BigQ.sub_norm a b.
Definition c_mul (a b : rat) : rat := BigQ.mul_norm a b.
Definition c_div (a b : rat) : rat := BigQ.div_norm a b.
Definition c_opp (a : rat) : rat := BigQ.opp a.
Definition c_inv (a : rat) : rat := BigQ.inv_norm a.
Definition c_is0 (a : rat) : bool := BigQ.eq_bool a BigQ.zero.
Definition c_eqb (a b : rat) : bool := BigQ.eq_bool a b.

Lemma i_of_ZK z : i_to_Z (i_of_Z z) = z. Proof. exact: BigZ.spec_of_Z. Qed.
Lemma i_zero_spec : i_to_Z i_zero = Z0. Proof. exact: BigZ.spec_0. Qed.
Lemma i_one_spec : i_to_Z i_one = Zpos xH. Proof. exact: BigZ.spec_1. Qed.
Lemma i_add_spec a b : i_to_Z (i_add a b) = Z.add (i_to_Z a) (i_to_Z b).
Proof. exact: BigZ.spec_add. Qed.
Lemma i_mul_spec a b : i_to_Z (i_mul a b) = Z.mul (i_to_Z a) (i_to_Z b).
Proof. exact: BigZ.spec_mul. Qed.
Lemma i_pow_spec b k : i_to_Z (i_pow b k) = Z.pow (Zpos b) (Z.of_nat k).
Proof. by rewrite /i_to_Z /i_pow BigZ.spec_pow !BigZ.spec_of_Z. Qed.
Lemma i_eqb_spec a b : i_eqb a b = Z.eqb (i_to_Z a) (i_to_Z b).
Proof. exact: BigZ.spec_eqb. Qed.
Lemma i_ltb_spec a b : i_ltb a b = Z.ltb (i_to_Z a) (i_to_Z b).
Proof. exact: BigZ.spec_ltb. Qed.
Lemma i_to_pos_spec a : i_to_pos a = Z.to_pos (i_to_Z a). Proof. by []. Qed.

Lemma c_zero_spec : Qeq (c_to_Q c_zero) (Qmake Z0 xH).
Proof. exact: BigQ.spec_0. Qed.
Lemma c_one_spec : Qeq (c_to_Q c_one) (Qmake (Zpos xH) xH).
Proof. exact: BigQ.spec_1. Qed.
Lemma c_of_int_spec a : Qeq (c_to_Q (c_of_int a)) (Qmake (i_to_Z a) xH).
Proof. exact: Qeq_refl. Qed.
Lemma c_of_Z_spec z : Qeq (c_to_Q (c_of_Z z)) (Qmake z xH).
Proof. by rewrite /c_to_Q /c_of_Z /= BigZ.spec_of_Z; exact: Qeq_refl. Qed.
Lemma c_add_spec a b :
  Qeq (c_to_Q (c_add a b)) (Qplus (c_to_Q a) (c_to_Q b)).
Proof. exact: BigQ.spec_add_norm. Qed.
Lemma c_sub_spec a b :
  Qeq (c_to_Q (c_sub a b)) (Qminus (c_to_Q a) (c_to_Q b)).
Proof. exact: BigQ.spec_sub_norm. Qed.
Lemma c_mul_spec a b :
  Qeq (c_to_Q (c_mul a b)) (Qmult (c_to_Q a) (c_to_Q b)).
Proof. exact: BigQ.spec_mul_norm. Qed.
Lemma c_div_spec a b :
  Qeq (c_to_Q (c_div a b)) (Qdiv (c_to_Q a) (c_to_Q b)).
Proof. exact: BigQ.spec_div_norm. Qed.
Lemma c_opp_spec a : Qeq (c_to_Q (c_opp a)) (Qopp (c_to_Q a)).
Proof. exact: BigQ.spec_opp. Qed.
Lemma c_inv_spec a : Qeq (c_to_Q (c_inv a)) (Qinv (c_to_Q a)).
Proof. exact: BigQ.spec_inv_norm. Qed.
Lemma c_eqb_spec a b : c_eqb a b -> Qeq (c_to_Q a) (c_to_Q b).
Proof. by rewrite /c_eqb BigQ.spec_eq_bool => /Qeq_bool_eq. Qed.
Lemma c_is0_spec a : c_is0 a -> Qeq (c_to_Q a) (Qmake Z0 xH).
Proof. by move/c_eqb_spec => H; apply: Qeq_trans H c_zero_spec. Qed.

End BigNum.
