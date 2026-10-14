(******************************************************************************)
(* Backend: the number backend of the normaliser.                             *)
(*   Q2F q        == the Stdlib rational q seen in F (Z2F, pos2F: Syntax.v)   *)
(*   NUM          == module type of backends: integers int, rationals rat,    *)
(*                   the operations i_..., c_... of the normaliser and their  *)
(*                   specification through i_to_Z, c_to_Q (exact on int, up   *)
(*                   to Qeq on rat); unspecified operations (division,        *)
(*                   square root, ...) only drive heuristics                  *)
(*   ZNum : NUM   == the Stdlib instance (int = Z, rat = Q kept reduced)      *)
(*   NumFacts N   == I2F, C2F (numbers of N seen in F), morphism lemmas       *)
(* Bases of radicals stay Stdlib positives (p_cmp, p_eqb).  The Bignums       *)
(* instance is in BigBackend.v.                                               *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation Z1 := (Zpos xH).

(* positives (bases of radicals) *)
Definition p_cmp (a b : positive) : comparison := Pos.compare a b.
Definition p_eqb (a b : positive) : bool := Pos.eqb a b.

Lemma p_cmpP a b : p_cmp a b = Eq -> a = b.
Proof. exact: Pos.compare_eq. Qed.

Lemma p_eqbP a b : p_eqb a b -> a = b.
Proof. by move/Pos.eqb_eq. Qed.

Section NumSound.

Variable F : numFieldType.
Local Open Scope ring_scope.

Lemma Z2F_opp z : Z2F F (Z.opp z) = - Z2F F z.
Proof. by case: z => [|p|p] //=; rewrite ?oppr0 ?opprK. Qed.

Lemma Z2F_nat k : Z2F F (Z.of_nat k) = k%:R.
Proof. by case: k => [|k] //=; rewrite /pos2F SuccNat2Pos.id_succ. Qed.

Lemma Z2F_subnat a b : Z2F F (Z.sub (Z.of_nat a) (Z.of_nat b)) = a%:R - b%:R.
Proof.
case: (leqP a b) => ab.
  have -> : Z.sub (Z.of_nat a) (Z.of_nat b) = Z.opp (Z.of_nat (b - a)).
    by move/ssrnat.leP: (ab) => ab'; rewrite Nat2Z.inj_sub //; lia.
  by rewrite Z2F_opp Z2F_nat natrB // opprB.
have -> : Z.sub (Z.of_nat a) (Z.of_nat b) = Z.of_nat (a - b).
  by move/ltnW/ssrnat.leP: (ab) => ab'; rewrite Nat2Z.inj_sub //; lia.
by rewrite Z2F_nat natrB // ltnW.
Qed.

Lemma Zdec z : exists a b, z = Z.sub (Z.of_nat a) (Z.of_nat b).
Proof. by exists (Z.to_nat z), (Z.to_nat (Z.opp z)); lia. Qed.

Lemma Z2F_add x y : Z2F F (Z.add x y) = Z2F F x + Z2F F y.
Proof.
have [a [b ->]] := Zdec x; have [c [d ->]] := Zdec y.
have -> : Z.add (Z.sub (Z.of_nat a) (Z.of_nat b))
                (Z.sub (Z.of_nat c) (Z.of_nat d)) =
          Z.sub (Z.of_nat (a + c)) (Z.of_nat (b + d)).
  by rewrite !Nat2Z.inj_add; lia.
by rewrite !Z2F_subnat !natrD opprD addrACA.
Qed.

Lemma Z2F_mul x y : Z2F F (Z.mul x y) = Z2F F x * Z2F F y.
Proof.
have [a [b ->]] := Zdec x; have [c [d ->]] := Zdec y.
have -> : Z.mul (Z.sub (Z.of_nat a) (Z.of_nat b))
                (Z.sub (Z.of_nat c) (Z.of_nat d)) =
          Z.sub (Z.of_nat (a * c + b * d)) (Z.of_nat (a * d + b * c)).
  by rewrite !Nat2Z.inj_add !Nat2Z.inj_mul; lia.
rewrite !Z2F_subnat !natrD !natrM mulrBl !mulrBr opprB.
by rewrite opprD addrACA addrC.
Qed.

Lemma Z2F1 : Z2F F Z1 = 1.
Proof. by rewrite /= /pos2F. Qed.

Lemma Z2F_eq0 c : Z.eqb c Z0 -> Z2F F c = 0.
Proof. by move/Z.eqb_eq->. Qed.

Lemma pos2F_ge0 b : 0 <= pos2F F b.
Proof. exact: ler0n. Qed.

Lemma Z2F_pow b q : Z2F F (Z.pow (Zpos b) (Z.of_nat q)) = pos2F F b ^+ q.
Proof.
elim: q => [|q IH]; first by rewrite expr0 Z2F1.
by rewrite Nat2Z.inj_succ Z.pow_succ_r ?Z2F_mul ?IH ?exprS //; lia.
Qed.

Lemma pos2F1 : pos2F F xH = 1.
Proof. by rewrite /pos2F. Qed.

(* rational coefficients *)

Definition Q2F (q : Q) : F := Z2F F (Qnum q) / pos2F F (Qden q).

Lemma pos2F_neq0 p : pos2F F p != 0.
Proof.
by rewrite /pos2F pnatr_eq0 -lt0n; apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
Qed.

Lemma pos2F_mul p q : pos2F F (Pos.mul p q) = pos2F F p * pos2F F q.
Proof. by rewrite /pos2F Pos2Nat.inj_mul natrM. Qed.

Lemma Q2F_Qeq q1 q2 : Qeq q1 q2 -> Q2F q1 = Q2F q2.
Proof.
case: q1 q2 => [n1 d1] [n2 d2]; rewrite /Qeq /Q2F /= => H.
apply/eqP; rewrite eqr_div ?pos2F_neq0 //.
rewrite -[pos2F F d2]/(Z2F F (Zpos d2)) -[pos2F F d1]/(Z2F F (Zpos d1)).
by rewrite -!Z2F_mul H.
Qed.

Lemma Q2F_red q : Q2F (Qred q) = Q2F q.
Proof. exact/Q2F_Qeq/Qred_correct. Qed.

Lemma Q2F_plus q1 q2 : Q2F (Qplus q1 q2) = Q2F q1 + Q2F q2.
Proof.
case: q1 q2 => [n1 d1] [n2 d2]; rewrite /Q2F /Qplus /=.
by rewrite addf_div ?pos2F_neq0 // Z2F_add !Z2F_mul pos2F_mul.
Qed.

Lemma Q2F_mult q1 q2 : Q2F (Qmult q1 q2) = Q2F q1 * Q2F q2.
Proof.
case: q1 q2 => [n1 d1] [n2 d2]; rewrite /Q2F /Qmult /=.
by rewrite mulf_div Z2F_mul pos2F_mul.
Qed.

Lemma Q2F_opp q : Q2F (Qopp q) = - Q2F q.
Proof. by case: q => [n d]; rewrite /Q2F /= Z2F_opp mulNr. Qed.

Lemma Q2F_Z z : Q2F (Qmake z xH) = Z2F F z.
Proof. by rewrite /Q2F /= pos2F1 divr1. Qed.

Lemma Q2F_Qinv q : Q2F (Qinv q) = (Q2F q)^-1.
Proof.
case: q => [[|n|n] d]; rewrite /Q2F /Qinv /=.
- by rewrite !mul0r invr0.
- by rewrite invf_div.
by rewrite !mulNr invrN invf_div.
Qed.

End NumSound.

Arguments Q2F {F} q.
Arguments Z2F_opp {F}.
Arguments Z2F_nat {F}.
Arguments Z2F_subnat {F}.
Arguments Z2F_add {F}.
Arguments Z2F_mul {F}.
Arguments Z2F1 {F}.
Arguments Z2F_eq0 {F}.
Arguments pos2F_ge0 {F}.
Arguments Z2F_pow {F}.
Arguments pos2F1 {F}.
Arguments pos2F_neq0 {F}.
Arguments pos2F_mul {F}.
Arguments Q2F_Qeq {F}.
Arguments Q2F_red {F}.
Arguments Q2F_plus {F}.
Arguments Q2F_mult {F}.
Arguments Q2F_opp {F}.
Arguments Q2F_Z {F}.
Arguments Q2F_Qinv {F}.

(* Number backends *)

Module Type NUM.

Parameter int : Type.
Parameter rat : Type.

(* conversions *)
Parameter i_to_Z : int -> Z.
Parameter i_of_Z : Z -> int.
Parameter c_to_Q : rat -> Q.

(* integers *)
Parameter i_zero : int.
Parameter i_one : int.
Parameter i_add : int -> int -> int.
Parameter i_mul : int -> int -> int.
Parameter i_pow : positive -> nat -> int.
Parameter i_eqb : int -> int -> bool.
Parameter i_ltb : int -> int -> bool.
Parameter i_rem : int -> int -> int.
Parameter i_div : int -> int -> int.
Parameter i_gcd : int -> int -> int.
Parameter i_succ : int -> int.
Parameter i_sqrt : int -> int.
Parameter i_to_pos : int -> positive.
Parameter i_to_nat : int -> nat.
Parameter i_size : int -> nat.

(* rationals *)
Parameter c_zero : rat.
Parameter c_one : rat.
Parameter c_of_int : int -> rat.
Parameter c_of_Z : Z -> rat.
Parameter c_add : rat -> rat -> rat.
Parameter c_sub : rat -> rat -> rat.
Parameter c_mul : rat -> rat -> rat.
Parameter c_div : rat -> rat -> rat.
Parameter c_opp : rat -> rat.
Parameter c_inv : rat -> rat.
Parameter c_is0 : rat -> bool.
Parameter c_eqb : rat -> rat -> bool.

Axiom i_of_ZK : forall z, i_to_Z (i_of_Z z) = z.
Axiom i_zero_spec : i_to_Z i_zero = Z0.
Axiom i_one_spec : i_to_Z i_one = Z1.
Axiom i_add_spec : forall a b,
  i_to_Z (i_add a b) = Z.add (i_to_Z a) (i_to_Z b).
Axiom i_mul_spec : forall a b,
  i_to_Z (i_mul a b) = Z.mul (i_to_Z a) (i_to_Z b).
Axiom i_pow_spec : forall b k,
  i_to_Z (i_pow b k) = Z.pow (Zpos b) (Z.of_nat k).
Axiom i_eqb_spec : forall a b, i_eqb a b = Z.eqb (i_to_Z a) (i_to_Z b).
Axiom i_ltb_spec : forall a b, i_ltb a b = Z.ltb (i_to_Z a) (i_to_Z b).
Axiom i_to_pos_spec : forall a, i_to_pos a = Z.to_pos (i_to_Z a).

Axiom c_zero_spec : Qeq (c_to_Q c_zero) (Qmake Z0 xH).
Axiom c_one_spec : Qeq (c_to_Q c_one) (Qmake Z1 xH).
Axiom c_of_int_spec : forall a,
  Qeq (c_to_Q (c_of_int a)) (Qmake (i_to_Z a) xH).
Axiom c_of_Z_spec : forall z, Qeq (c_to_Q (c_of_Z z)) (Qmake z xH).
Axiom c_add_spec : forall a b,
  Qeq (c_to_Q (c_add a b)) (Qplus (c_to_Q a) (c_to_Q b)).
Axiom c_sub_spec : forall a b,
  Qeq (c_to_Q (c_sub a b)) (Qminus (c_to_Q a) (c_to_Q b)).
Axiom c_mul_spec : forall a b,
  Qeq (c_to_Q (c_mul a b)) (Qmult (c_to_Q a) (c_to_Q b)).
Axiom c_div_spec : forall a b,
  Qeq (c_to_Q (c_div a b)) (Qdiv (c_to_Q a) (c_to_Q b)).
Axiom c_opp_spec : forall a, Qeq (c_to_Q (c_opp a)) (Qopp (c_to_Q a)).
Axiom c_inv_spec : forall a, Qeq (c_to_Q (c_inv a)) (Qinv (c_to_Q a)).
Axiom c_is0_spec : forall a, c_is0 a -> Qeq (c_to_Q a) (Qmake Z0 xH).
Axiom c_eqb_spec : forall a b, c_eqb a b -> Qeq (c_to_Q a) (c_to_Q b).

End NUM.

(* The Stdlib instance: Z and Q (kept reduced by Qred) *)
Module ZNum <: NUM.

Definition int := Z.
Definition rat := Q.
Definition i_to_Z (a : int) : Z := a.
Definition i_of_Z (z : Z) : int := z.
Definition c_to_Q (a : rat) : Q := a.

Definition i_zero : int := Z0.
Definition i_one : int := Z1.
Definition i_add (a b : int) : int := Z.add a b.
Definition i_mul (a b : int) : int := Z.mul a b.
Definition i_pow (b : positive) (k : nat) : int :=
  Z.pow (Zpos b) (Z.of_nat k).
Definition i_eqb (a b : int) : bool := Z.eqb a b.
Definition i_ltb (a b : int) : bool := Z.ltb a b.
Definition i_rem (a b : int) : int := Z.rem a b.
Definition i_div (a b : int) : int := Z.div a b.
Definition i_gcd (a b : int) : int := Z.gcd a b.
Definition i_succ (a : int) : int := Z.succ a.
Definition i_sqrt (a : int) : int := Z.sqrt a.
Definition i_to_pos (a : int) : positive := Z.to_pos a.
Definition i_to_nat (a : int) : nat := Z.to_nat a.
Definition i_size (a : int) : nat := Pos.size_nat (Z.to_pos a).

Definition c_zero : rat := Qmake Z0 xH.
Definition c_one : rat := Qmake Z1 xH.
Definition c_of_int (a : int) : rat := Qmake a xH.
Definition c_of_Z (z : Z) : rat := Qmake z xH.
Definition c_add (a b : rat) : rat := Qred (Qplus a b).
Definition c_sub (a b : rat) : rat := Qred (Qminus a b).
Definition c_mul (a b : rat) : rat := Qred (Qmult a b).
Definition c_div (a b : rat) : rat := Qred (Qdiv a b).
Definition c_opp (a : rat) : rat := Qopp a.
Definition c_inv (a : rat) : rat := Qred (Qinv a).
Definition c_is0 (a : rat) : bool := Z.eqb (Qnum a) Z0.
Definition c_eqb (a b : rat) : bool :=
  Z.eqb (Qnum a) (Qnum b) && Pos.eqb (Qden a) (Qden b).

Lemma i_of_ZK z : i_to_Z (i_of_Z z) = z. Proof. by []. Qed.
Lemma i_zero_spec : i_to_Z i_zero = Z0. Proof. by []. Qed.
Lemma i_one_spec : i_to_Z i_one = Z1. Proof. by []. Qed.
Lemma i_add_spec a b : i_to_Z (i_add a b) = Z.add (i_to_Z a) (i_to_Z b).
Proof. by []. Qed.
Lemma i_mul_spec a b : i_to_Z (i_mul a b) = Z.mul (i_to_Z a) (i_to_Z b).
Proof. by []. Qed.
Lemma i_pow_spec b k : i_to_Z (i_pow b k) = Z.pow (Zpos b) (Z.of_nat k).
Proof. by []. Qed.
Lemma i_eqb_spec a b : i_eqb a b = Z.eqb (i_to_Z a) (i_to_Z b).
Proof. by []. Qed.
Lemma i_ltb_spec a b : i_ltb a b = Z.ltb (i_to_Z a) (i_to_Z b).
Proof. by []. Qed.
Lemma i_to_pos_spec a : i_to_pos a = Z.to_pos (i_to_Z a). Proof. by []. Qed.

Lemma c_zero_spec : Qeq (c_to_Q c_zero) (Qmake Z0 xH). Proof. by []. Qed.
Lemma c_one_spec : Qeq (c_to_Q c_one) (Qmake Z1 xH). Proof. by []. Qed.
Lemma c_of_int_spec a : Qeq (c_to_Q (c_of_int a)) (Qmake (i_to_Z a) xH).
Proof. by []. Qed.
Lemma c_of_Z_spec z : Qeq (c_to_Q (c_of_Z z)) (Qmake z xH). Proof. by []. Qed.
Lemma c_add_spec a b :
  Qeq (c_to_Q (c_add a b)) (Qplus (c_to_Q a) (c_to_Q b)).
Proof. exact: Qred_correct. Qed.
Lemma c_sub_spec a b :
  Qeq (c_to_Q (c_sub a b)) (Qminus (c_to_Q a) (c_to_Q b)).
Proof. exact: Qred_correct. Qed.
Lemma c_mul_spec a b :
  Qeq (c_to_Q (c_mul a b)) (Qmult (c_to_Q a) (c_to_Q b)).
Proof. exact: Qred_correct. Qed.
Lemma c_div_spec a b :
  Qeq (c_to_Q (c_div a b)) (Qdiv (c_to_Q a) (c_to_Q b)).
Proof. exact: Qred_correct. Qed.
Lemma c_opp_spec a : Qeq (c_to_Q (c_opp a)) (Qopp (c_to_Q a)).
Proof. by rewrite /Qeq. Qed.
Lemma c_inv_spec a : Qeq (c_to_Q (c_inv a)) (Qinv (c_to_Q a)).
Proof. exact: Qred_correct. Qed.
Lemma c_is0_spec a : c_is0 a -> Qeq (c_to_Q a) (Qmake Z0 xH).
Proof. by case: a => n d /Z.eqb_eq /= ->; rewrite /Qeq. Qed.
Lemma c_eqb_spec a b : c_eqb a b -> Qeq (c_to_Q a) (c_to_Q b).
Proof.
case: a b => [n1 d1] [n2 d2] /andP[/Z.eqb_eq /= -> /Pos.eqb_eq /= ->].
by rewrite /Qeq.
Qed.

End ZNum.

(* Derived facts: the numbers of a backend seen in a numFieldType *)
Module NumFacts (Import N : NUM).

Definition coef := rat.

Section Facts.

Variable F : numFieldType.
Local Open Scope ring_scope.

Definition I2F (a : int) : F := Z2F F (i_to_Z a).
Definition C2F (a : rat) : F := Q2F (c_to_Q a).

Lemma I2F_i_one : I2F i_one = 1.
Proof. by rewrite /I2F i_one_spec /= /pos2F. Qed.

Lemma I2F_i_mul a b : I2F (i_mul a b) = I2F a * I2F b.
Proof. by rewrite /I2F i_mul_spec Z2F_mul. Qed.

Lemma I2F_i_pow b k : I2F (i_pow b k) = pos2F F b ^+ k.
Proof. by rewrite /I2F i_pow_spec Z2F_pow. Qed.

Lemma i_eqbP a b : i_eqb a b -> i_to_Z a = i_to_Z b.
Proof. by rewrite i_eqb_spec => /Z.eqb_eq. Qed.

Lemma C2F_c_zero : C2F c_zero = 0.
Proof. by rewrite /C2F (Q2F_Qeq _ _ c_zero_spec) /Q2F /= mul0r. Qed.

Lemma C2F_c_one : C2F c_one = 1.
Proof. by rewrite /C2F (Q2F_Qeq _ _ c_one_spec) /Q2F /= /pos2F divr1. Qed.

Lemma C2F_c_of_int a : C2F (c_of_int a) = I2F a.
Proof. by rewrite /C2F (Q2F_Qeq _ _ (c_of_int_spec a)) Q2F_Z. Qed.

Lemma C2F_c_of_Z z : C2F (c_of_Z z) = Z2F F z.
Proof. by rewrite /C2F (Q2F_Qeq _ _ (c_of_Z_spec z)) Q2F_Z. Qed.

Lemma C2F_c_add a b : C2F (c_add a b) = C2F a + C2F b.
Proof. by rewrite /C2F (Q2F_Qeq _ _ (c_add_spec a b)) Q2F_plus. Qed.

Lemma C2F_c_sub a b : C2F (c_sub a b) = C2F a - C2F b.
Proof.
by rewrite /C2F (Q2F_Qeq _ _ (c_sub_spec a b)) /Qminus Q2F_plus Q2F_opp.
Qed.

Lemma C2F_c_mul a b : C2F (c_mul a b) = C2F a * C2F b.
Proof. by rewrite /C2F (Q2F_Qeq _ _ (c_mul_spec a b)) Q2F_mult. Qed.

Lemma C2F_c_div a b : C2F (c_div a b) = C2F a / C2F b.
Proof.
by rewrite /C2F (Q2F_Qeq _ _ (c_div_spec a b)) /Qdiv Q2F_mult Q2F_Qinv.
Qed.

Lemma C2F_c_opp a : C2F (c_opp a) = - C2F a.
Proof. by rewrite /C2F (Q2F_Qeq _ _ (c_opp_spec a)) Q2F_opp. Qed.

Lemma C2F_c_inv a : C2F (c_inv a) = (C2F a)^-1.
Proof. by rewrite /C2F (Q2F_Qeq _ _ (c_inv_spec a)) Q2F_Qinv. Qed.

Lemma c_is0P a : c_is0 a -> C2F a = 0.
Proof.
by move/c_is0_spec/Q2F_Qeq; rewrite /C2F => ->; rewrite /Q2F /= mul0r.
Qed.

Lemma c_eqbP a b : c_eqb a b -> C2F a = C2F b.
Proof. by move/c_eqb_spec/Q2F_Qeq; rewrite /C2F. Qed.

End Facts.

Arguments C2F {F} a.
Arguments I2F_i_one {F}.
Arguments I2F_i_mul {F}.
Arguments I2F_i_pow {F}.
Arguments C2F_c_zero {F}.
Arguments C2F_c_one {F}.
Arguments C2F_c_of_int {F}.
Arguments C2F_c_of_Z {F}.
Arguments C2F_c_add {F}.
Arguments C2F_c_sub {F}.
Arguments C2F_c_mul {F}.
Arguments C2F_c_div {F}.
Arguments C2F_c_opp {F}.
Arguments C2F_c_inv {F}.
Arguments c_is0P {F}.
Arguments c_eqbP {F}.

End NumFacts.
