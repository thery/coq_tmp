(******************************************************************************)
(* TrigTac: radcan_trig, trigonometric identities on the reals of Stdlib.    *)
(* Goals: equalities between expressions built from numerals, variables,    *)
(* + - * / ^, sqrt of numerals, and cos, sin, tan of angles                 *)
(* (integer combinations of variables) + (rational multiple of PI).         *)
(*   radcan_trig == unfolds tan, clears the denominators on R               *)
(*        (field_simplify_eq: conditions p <> 0, stated on R), then         *)
(*        trig_core on the polynomial equation; each condition is closed    *)
(*        by trig_cond1 when it can be, otherwise left to the user          *)
(*   trig_core   == to R[i] (trig_realC, trig_push: %:C through the         *)
(*        operations, cos and sin through E), angles through E            *)
(*        (trig_angles: E of a sum, a multiple, a multiple of PI as        *)
(*        powers of E x and of n.-root (-1)), each E x made a variable u   *)
(*        with u != 0 and both sides multiplied by its largest negative    *)
(*        power (trig_clear), then radcan; the conditions u != 0 are       *)
(*        closed (trig_nzE)                                                *)
(*   trig_cond1  == a condition p <> 0: hypothesis, numeral (lra), power or *)
(*        product of such, closed cos t / sin t (trig_sign), or p = q,     *)
(*        p = - q, q = p * m for hypotheses q <> 0, m <> 0 (by trig_core)  *)
(* Numerals are written pos2F R[i] p on R[i]: the reification of radcan   *)
(* then converts them for free (with mathcomp numerals 2%:R on R[i] the    *)
(* conversion costs seconds).  The file exports ssrnum, complex, Rstruct   *)
(* and TrigBridge: radcan needs their canonical instances on R[i].         *)
(******************************************************************************)

From Stdlib Require Import Reals Lra QArith.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Export ssrnum.
From mathcomp.real_closed Require Export complex.
From Radcan Require Export Rstruct.
From Radcan Require Import PosRoot Syntax Radcan Tactic RootRstd UnitArc.
From RadcanTrig Require Export TrigBridge.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope complex_scope.

(* 'i is the principal square root of -1 *)
Lemma rootC2N1 : 2.-root (-1 : R[i]) = 'i.
Proof.
set w := 2.-root (-1 : R[i]).
have w2 : w ^+ 2 = -1 by rewrite /w rootCK.
have hIm : 0 < 'Im w := @Im_rootC_N1_gt0 _ 2 isT.
have : (w - 'i) * (w + 'i) = 0 by rewrite -subr_sqr w2 sqr_i subrr.
move/eqP; rewrite mulf_eq0 => /orP[]; first by rewrite subr_eq0 => /eqP.
rewrite addr_eq0 => /eqP wE; move: hIm; rewrite wE.
by rewrite -complexIm /= ltcR ltr0N1.
Qed.

(* %:C on the numerals, as pos2F *)
Lemma RC_Z0 : (IZR Z0)%:C = 0 :> R[i].
Proof. exact: rmorph0. Qed.

Lemma RC_Zpos p : (IZR (Zpos p))%:C = pos2F R[i] p.
Proof. by rewrite IZR_posE /pos2F rmorph_nat. Qed.

Lemma RC_Zneg p : (IZR (Zneg p))%:C = - pos2F R[i] p.
Proof. by rewrite IZR_negE rmorphN /pos2F rmorph_nat. Qed.

Lemma RC_R0 : R0%:C = 0 :> R[i].
Proof. exact: rmorph0. Qed.

Lemma RC_R1 : R1%:C = pos2F R[i] 1.
Proof. by rewrite /pos2F rmorph1. Qed.

(* sqrt a, a >= 0, is the principal square root of a on R[i] *)
Lemma RC_sqrt (a : R) : Rle 0 a -> (sqrt a)%:C = 2.-root (a%:C).
Proof.
move=> a0; have s0 : Rle 0 (sqrt a) := sqrt_pos a.
have e : a%:C = ((sqrt a)%:C) ^+ 2.
  by rewrite -rmorphXn expr2 -RmultE sqrt_sqrt.
by rewrite e sqrCK // lecR; apply/RleP.
Qed.

Lemma RC_sqrtp p : (sqrt (IZR (Zpos p)))%:C = 2.-root (pos2F R[i] p).
Proof. by rewrite RC_sqrt ?RC_Zpos //; apply: IZR_le. Qed.

(* cos and sin through E, numerals as pos2F, 'i as 2.-root (-1) *)
Lemma cos_Ep x : (cos x)%:C = (E x + (E x)^-1) / pos2F R[i] 2.
Proof. by rewrite cos_E. Qed.

Lemma sin_Ep x : (sin x)%:C =
  (E x - (E x)^-1) / (pos2F R[i] 2 * 2.-root (- pos2F R[i] 1)).
Proof. by rewrite [pos2F _ 1]/= rootC2N1 sin_E. Qed.

(* the transfer, with the equation stated on R[i] itself (not on the sort
   of a weaker structure): radcan then infers the numFieldType of R[i] *)
Lemma trig_realC (a b : R) : @eq R[i] a%:C b%:C -> a = b.
Proof. exact: realC_inj. Qed.

(* E of the angles: sums, opposites, integer multiples, PI *)
Lemma E_add a b : E (Rplus a b) = E a * E b.
Proof. by rewrite EM. Qed.

Lemma E_opp a : E (Ropp a) = (E a)^-1.
Proof. by rewrite EV. Qed.

Lemma E_sub a b : E (Rminus a b) = E a * (E b)^-1.
Proof. by rewrite EV EM. Qed.

Lemma E_posl p a : E (IZR (Zpos p) * a) = E a ^+ Pos.to_nat p.
Proof. by rewrite EX INR_IPR. Qed.

Lemma E_posr p a : E (a * IZR (Zpos p)) = E a ^+ Pos.to_nat p.
Proof. by rewrite Rmult_comm E_posl. Qed.

Lemma E_negl p a : E (IZR (Zneg p) * a) = (E a ^+ Pos.to_nat p)^-1.
Proof. by rewrite -E_posl -E_opp IZR_NEG Ropp_mult_distr_l. Qed.

Lemma E_negr p a : E (a * IZR (Zneg p)) = (E a ^+ Pos.to_nat p)^-1.
Proof. by rewrite Rmult_comm E_negl. Qed.

Lemma E_Z0 : E (IZR Z0) = 1.
Proof. exact: E0. Qed.

Lemma E_PIn : E PI = - pos2F R[i] 1.
Proof. by rewrite E_PI. Qed.

Lemma E_PI1n : E (PI / IZR (Zpos 1)) = - pos2F R[i] 1.
Proof. by rewrite Rdiv_1_r E_PIn. Qed.

Lemma E_PIdivn p :
  E (PI / IZR (Zpos p)) = (Pos.to_nat p).-root (- pos2F R[i] 1).
Proof. by rewrite E_rootZ. Qed.

(* both sides multiplied by E x ^+ n, to clear the negative powers *)
Lemma trig_mulE x n (a b : R[i]) :
  @eq R[i] (E x ^+ n * a) (E x ^+ n * b) -> @eq R[i] a b.
Proof.
by move=> h; apply: (mulfI _ h); apply: expf_neq0; exact: E_neq0.
Qed.

Ltac trig_q t :=
  let bin a b k :=
    let p := trig_q a in let q := trig_q b in
    lazymatch p with (?pa, ?ca) =>
    lazymatch q with (?pb, ?cb) => k pa ca pb cb end end in
  lazymatch t with
  | PI => constr:((inject_Z 1, inject_Z 0))
  | IZR ?z => constr:((inject_Z 0, inject_Z z))
  | INR ?n => constr:((inject_Z 0, inject_Z (Z.of_nat n)))
  | Rplus ?a ?b =>
      bin a b ltac:(fun pa ca pb cb => constr:((Qplus pa pb, Qplus ca cb)))
  | Rminus ?a ?b =>
      bin a b ltac:(fun pa ca pb cb => constr:((Qminus pa pb, Qminus ca cb)))
  | Rmult ?a ?b =>
      bin a b ltac:(fun pa ca pb cb =>
        constr:((Qplus (Qmult pa cb) (Qmult ca pb), Qmult ca cb)))
  | Rdiv ?a ?b =>
      bin a b ltac:(fun pa ca pb cb => constr:((Qdiv pa cb, Qdiv ca cb)))
  | Ropp ?a =>
      let p := trig_q a in
      lazymatch p with (?pa, ?ca) => constr:((Qopp pa, Qopp ca)) end
  | Rinv ?a =>
      let p := trig_q a in
      lazymatch p with (?pa, ?ca) => constr:((inject_Z 0, Qinv ca)) end
  end.

(* one closed angle E t, t = (k / n) PI, rewritten as E (k * (PI / n)) *)
Ltac trig_pi_step :=
  match goal with
  | |- context [E ?t] =>
      lazymatch t with
      | PI => fail
      | Rdiv PI (IZR (Zpos _)) => fail
      | _ => idtac
      end;
      let p := trig_q t in
      lazymatch p with (?pa, ?ca) =>
      lazymatch eval vm_compute in (Qeq_bool ca (inject_Z 0)) with
      | true =>
          lazymatch eval vm_compute in (Qred pa) with
          | Qmake ?k ?n =>
              let e := fresh "e" in
              (have e : t = Rmult (IZR k) (Rdiv PI (IZR (Zpos n))) by field);
              rewrite [in E t]e; clear e
          end
      end end
  end.

(* E of a sum, a difference, an opposite, an integer multiple, a multiple
   of PI: products, inverses and powers of the E x and of n.-root (-1).
   One rewrite at a time, the laws of PI first: PI is a product 2 * _ by
   definition, and E_posl would otherwise unfold it *)
Ltac trig_E_step :=
  first [ rewrite E_PIn | rewrite E_PI1n | rewrite E_PIdivn | rewrite E_Z0
        | rewrite E_add | rewrite E_sub | rewrite E_opp
        | rewrite E_posl | rewrite E_posr | rewrite E_negl | rewrite E_negr ].

Ltac trig_angles := repeat first [trig_E_step | trig_pi_step].

(* %:C through the operations of Stdlib, cos and sin through E *)
Ltac trig_push :=
  repeat progress rewrite ?realC_sub ?realC_div ?realC_add ?realC_opp
    ?realC_mul ?realC_inv ?realC_pow ?RC_Z0 ?RC_R0 ?RC_R1 ?RC_sqrtp ?RC_Zpos
    ?RC_Zneg ?realC_INR ?cos_Ep ?sin_Ep.

(* (p, n): bounds on the largest positive and negative degree of the
   atom u in the monomials of t (a Laurent polynomial in u) *)
Ltac trig_deg u t :=
  let bin a b k :=
    let p := trig_deg u a in let q := trig_deg u b in
    lazymatch p with (?pa, ?na) =>
    lazymatch q with (?pb, ?nb) => k pa na pb nb end end in
  lazymatch constr:((t, u)) with
  | (?v, ?v) => constr:((1, 0)%nat)
  | _ =>
  lazymatch t with
  | ?a + ?b =>
      bin a b ltac:(fun pa na pb nb => constr:((Nat.max pa pb, Nat.max na nb)))
  | ?a * ?b =>
      bin a b ltac:(fun pa na pb nb => constr:((pa + pb, na + nb)%nat))
  | - ?a => trig_deg u a
  | ?a ^-1 =>
      let p := trig_deg u a in
      lazymatch p with (?pa, ?na) => constr:((na, pa)) end
  | ?a ^+ ?k =>
      let p := trig_deg u a in
      lazymatch p with (?pa, ?na) => constr:((pa * k, na * k)%nat) end
  | _ => constr:((0, 0)%nat)
  end end.

(* each atom E x becomes a variable u with u != 0, and both sides are
   multiplied by u ^+ n, n the largest negative degree of u: radcan then
   compares polynomials in u, not Laurent polynomials *)
Ltac trig_clear :=
  repeat match goal with
  | |- context [E ?x] =>
      lazymatch goal with
      | |- ?l = ?r =>
          let p := trig_deg (E x) l in let q := trig_deg (E x) r in
          lazymatch p with (_, ?nl) =>
          lazymatch q with (_, ?nr) =>
          let n := eval vm_compute in (Nat.max nl nr) in
          lazymatch n with
          | O => idtac
          | _ => apply: (trig_mulE x n)
          end end end
      end;
      let u := fresh "u" in let hu := fresh "hu" in
      move: (E_neq0 x); move: (E x) => u hu
  end.

(* the conditions u != 0 on the atoms (products, powers, inverses) *)
Ltac trig_nzE :=
  repeat first
    [ match goal with h : is_true (?v != _) |- is_true (?v != _) => exact: h end
    | apply: mulf_neq0 | apply: expf_neq0 | rewrite invr_eq0 ].

(* a polynomial goal on R: to R[i], then radcan; the conditions u != 0
   are closed *)
Ltac trig_core :=
  apply: trig_realC; trig_push; trig_angles; trig_clear;
  first [radcan | fail 1 "radcan_trig: the normal forms differ"];
  try by trig_nzE.

(* a closed condition cos t <> 0 or sin t <> 0, t a multiple of PI: the
   sign of cos or sin on the interval of t (lra with 0 < PI) *)
Ltac trig_sign :=
  first
  [ apply: Rgt_not_eq; apply: cos_gt_0; have := PI_RGT_0; lra
  | apply: Rlt_not_eq; apply: cos_lt_0; have := PI_RGT_0; lra
  | apply: Rgt_not_eq; apply: sin_gt_0; have := PI_RGT_0; lra
  | apply: Rlt_not_eq; apply: sin_lt_0; have := PI_RGT_0; lra ].

(* a denominator condition p <> 0: a hypothesis, a numeral, a power or a
   product of such conditions, a closed cos or sin (trig_sign), p = q or
   p = - q for a hypothesis q <> 0, or q = p * m for two hypotheses
   q <> 0, m <> 0 (the equations proved by trig_core); else left *)
Ltac trig_cond1 :=
  first
  [ assumption
  | solve [lra]
  | solve [trig_sign]
  | apply: pow_nonzero; trig_cond1
  | apply: Rmult_integral_contrapositive_currified; trig_cond1
  | match goal with
    | h : ?q <> IZR Z0 |- ?p <> IZR Z0 =>
        let e := fresh "e" in
        (have e : p = q by solve [trig_core]);
        rewrite e; exact: h
    | h : ?q <> IZR Z0 |- ?p <> IZR Z0 =>
        let e := fresh "e" in
        (have e : p = Ropp q by solve [trig_core]);
        rewrite e; exact: Ropp_neq_0_compat
    | h : ?q <> IZR Z0, h' : ?m <> IZR Z0 |- ?p <> IZR Z0 =>
        let e := fresh "e" in let hp := fresh "hp" in
        (have e : q = Rmult p m by solve [trig_core]);
        move=> hp; apply: h; rewrite e hp; exact: Rmult_0_l
    end
  | idtac ].

Ltac trig_conds :=
  repeat match goal with |- _ /\ _ => split end; trig_cond1.

(* the tactic: tan unfolded, denominators cleared by field_simplify_eq
   (conditions p <> 0 on R), then trig_core *)
Ltac radcan_trig :=
  rewrite ?/tan; first [field_simplify_eq | idtac];
  [trig_core | trig_conds ..].
