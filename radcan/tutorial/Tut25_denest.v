(******************************************************************************)
(* Tutorial 25: denesting depth-two square roots (Denest.v, M19 phases 1-5).  *)
(*   denest_at r     == rewrites one proot r 2 t, t of the form a + b sqrt c, *)
(*                      into its candidate (denest_sound), then radcan        *)
(*   radcan_denest r == the whole goal through radcan_eq_denest               *)
(*   denest_atv r    == one proot r 2 t with variables (denestv_eq_refined),  *)
(*                      its refined conditions as the last goal               *)
(*   radcan_denestc r == the whole goal, refined conditions                   *)
(*                      (radcan_eq_denest_refined)                            *)
(*   denest_atm r    == denest_at with the phase 4 finder (several roots in   *)
(*                      the radicand, denest_findm)                           *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootR Syntax Radcan Refine Tactic Denest.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* one nested root: reify its radicand t, find the candidate c, check
   denest_ok e c by vm_compute (the square by radcan_check, the sign by
   sq_nonneg), then rewrite with denest_sound: proot r 2 t = candidate *)
Ltac denest_at r :=
  match goal with
  | |- context [proot r 2 ?t] =>
    let T := type of t in
    let p := radcan_reify_term r t (@nil T) in
    lazymatch p with (?e, ?env) =>
      let c := eval vm_compute in (denest_find e) in
      lazymatch c with
      | Some ?c =>
        let H := fresh "H" in let h := fresh "h" in
        (have H : denest_ok e c by vm_compute);
        have h : proot r 2 t = rinterp r env (dc_rexpr c) :=
          denest_sound r env H;
        rewrite h {h H} /dc_rexpr /=
      end
    end
  end.

(* the whole goal at once: radcan_check on the denested sides *)
Ltac radcan_denest r :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
    let c := eval vm_compute in (radcan_check_denest e1 e2) in
    lazymatch c with
    | Some ?cs =>
      apply: (@radcan_eq_denest _ r env e1 e2 cs);
        [vm_compute; reflexivity | radcan_split_conds]
    | None => fail "radcan_denest: the normal forms differ"
    end
  end.

Section Denest.
Variables (F : numFieldType) (r : posroot F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* for the normaliser alone \sqrt (3 + 2 sqrt 2) is an atom; radcan
   denests it through its pre-pass (Prepass.v, denest_rwc) *)
Lemma d0 : \sqrt (3 + 2 * \sqrt 2) = 1 + \sqrt 2.
Proof. radcan. Qed.

Lemma d1 : \sqrt (3 + 2 * \sqrt 2) = 1 + \sqrt 2.
Proof. denest_at r. radcan. Qed.

Lemma d2 : \sqrt (5 + 2 * \sqrt 6) = \sqrt 2 + \sqrt 3.
Proof. denest_at r. radcan. Qed.

(* sign certificate: sqrt 3 - 1 >= 0 needs sqrt 3 >= 1 *)
Lemma d3 : \sqrt (4 - 2 * \sqrt 3) = \sqrt 3 - 1.
Proof. denest_at r. radcan. Qed.

Lemma d4 : \sqrt (7 - 4 * \sqrt 3) = 2 - \sqrt 3.
Proof. denest_at r. radcan. Qed.

(* rational coefficients: sqrt (3/2 + sqrt 2) = 1 + sqrt 2 / 2 *)
Lemma d5 : \sqrt (3 / 2 + \sqrt 2) = 1 + \sqrt 2 / 2.
Proof. denest_at r. radcan. Qed.

(* the whole-goal version, several nested roots *)
Lemma d6 : \sqrt (3 + 2 * \sqrt 2) - \sqrt (3 - 2 * \sqrt 2)
  = 2.
Proof. radcan_denest r. Qed.

Lemma d7 : \sqrt (12 + 6 * \sqrt 3) * \sqrt (4 - 2 * \sqrt 3)
  = 2 * \sqrt 3.
Proof. radcan_denest r. Qed.

(* sqrt (1 + sqrt 2) does not denest: 1 - 2 = -1 is not a square *)
Goal \sqrt (1 + \sqrt 2) = 0.
Proof. Fail denest_at r. Abort.

(* it stays as it is, and radcan_denest still proves what radcan proves *)
(* (the condition 0 <= sqrt 2 + 1 of the square of a root is left) *)
Lemma d8 : \sqrt (1 + \sqrt 2) ^+ 2 = 1 + \sqrt 2.
Proof. radcan_denest r. by rewrite addr_ge0 ?proot_ge0. Qed.

(* a wrong candidate is refused: sqrt (4 - 2 sqrt 3) is not 1 - sqrt 3 *)
Goal \sqrt (4 - 2 * \sqrt 3) = 1 - \sqrt 3.
Proof. Fail radcan_denest r. Abort.

End Denest.

(* on a real closed field, with rootR *)
Lemma rc_denest (R : rcfType) :
  rootR 2 (5 - 2 * rootR 2 6) = rootR 2 3 - rootR 2 (2 : R).
Proof. radcan_denest (rootR_posroot R). Qed.

(* Phase 3: radicands with variables (Denest.v, denestv).  The radicand is
   A + B * s with s a product of square roots, s ^ 2 = C, and
   A ^ 2 - B ^ 2 C = d ^ 2 a perfect square: candidate
   sqrt ((A + d) / 2) +- sqrt ((A - d) / 2), checked by squaring, under
   conditions (refined by Refine.v) *)

(* one nested root, the conditions left as the last goal *)
Ltac denest_atv r :=
  match goal with
  | |- context [proot r 2 ?t] =>
    let T := type of t in
    let p := radcan_reify_term r t (@nil T) in
    lazymatch p with (?e, ?env) =>
      let c := eval vm_compute in (denestv e) in
      lazymatch c with
      | Some (?c, ?cs) =>
        let rcs := eval vm_compute in (refine cs) in
        let H := fresh "H" in let Hr := fresh "Hr" in let hc := fresh "hc" in
        (have H : denestv e = Some (c, cs) by vm_compute);
        (have Hr : refine cs = rcs by vm_compute);
        have hc : all_rconds T (proot r) env rcs; last first;
        [ let h := fresh "h" in
          have h : proot r 2 t = rinterp r env c :=
            denestv_eq_refined H Hr hc;
          rewrite h {h hc H Hr} /=; radcan_numerals
        | clear H Hr; radcan_split_rconds ]
      end
    end
  end.

(* the whole goal, refined conditions *)
Ltac radcan_denestc r :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
    let c := eval vm_compute in (radcan_check_denest e1 e2) in
    lazymatch c with
    | Some ?cs =>
      let rcs := eval vm_compute in (refine cs) in
      apply: (@radcan_eq_denest_refined _ r env e1 e2 cs rcs);
        [vm_compute; reflexivity | vm_compute; reflexivity
        | radcan_split_rconds]
    | None => fail "radcan_denestc: the normal forms differ"
    end
  end.

Section DenestVar.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* the condition 0 <= 1 + sqrt (x - 1) of the candidate is dropped (roots
   are nonnegative), 0 <= x - 1 is refined into 1 <= x; radcan does it too,
   through its pre-pass *)
Lemma v0 (hx : 1 <= x) :
  \sqrt (x + 2 * \sqrt (x - 1)) = 1 + \sqrt (x - 1).
Proof. radcan. exact: hx. Qed.

Lemma v1 (hx : 1 <= x) :
  \sqrt (x + 2 * \sqrt (x - 1)) = 1 + \sqrt (x - 1).
Proof. radcan_denestc r. exact: hx. Qed.

(* one root at a time: the conditions come last *)
Lemma v1' (hx : 1 <= x) :
  \sqrt (x + 2 * \sqrt (x - 1)) = 1 + \sqrt (x - 1).
Proof. denest_atv r. - radcan. - exact: hx. Qed.

(* the sign of sqrt (x - 1) - 1 is the condition 0 <= (x - 1) - 1 *)
Lemma v2 (hx : 2 <= x) :
  \sqrt (x - 2 * \sqrt (x - 1)) = \sqrt (x - 1) - 1.
Proof. radcan_denestc r. exact: hx. Qed.

Lemma v3 (hx : 1 <= x) : \sqrt (2 * x + 2 * \sqrt (x ^+ 2 - 1)) =
  \sqrt (x + 1) + \sqrt (x - 1).
Proof. radcan_denestc r. exact: hx. Qed.

Lemma v4 (hx : 0 <= x) (hy : 0 <= y) :
  \sqrt (x + y + 2 * \sqrt (x * y)) = \sqrt x + \sqrt y.
Proof. radcan_denestc r. - exact: hx. - exact: hy. Qed.

(* B = 2 x is not constant: the sign of x is a condition of the check *)
Lemma v5 (hx : 0 <= x) (hy : 0 <= y) :
  \sqrt (x ^+ 2 + y + 2 * x * \sqrt y) = x + \sqrt y.
Proof. radcan_denestc r. - exact: hx. - exact: hy. Qed.

(* two nested roots in one goal *)
Lemma v6 (hx : 2 <= x) :
  \sqrt (x + 2 * \sqrt (x - 1)) - \sqrt (x - 2 * \sqrt (x - 1))
  = 2.
Proof. radcan_denestc r. exact: hx. Qed.

(* sqrt (x + sqrt x) does not denest: x ^ 2 - x is not a square *)
Goal \sqrt (x + \sqrt x) = 0.
Proof. Fail denest_atv r. Fail radcan_denestc r. Abort.

End DenestVar.

(* Phase 4: several square roots in the radicand (Denest.v, denest_findm).
   The candidate sum_i c_i sqrt p_i has k terms when the radicand has
   k (k - 1) / 2 roots (k = 3, 4, 5), the p_i products of their bases:
   c_i c_j is read from the term of sqrt (p_i p_j), c_1 ^ 2 from
   c_1 c_2 * c_1 c_3 / c_2 c_3; it is checked by squaring and by the sign
   certificate (denest_ok), as in phase 1 *)

(* denest_at with the phase 4 finder *)
Ltac denest_atm r :=
  match goal with
  | |- context [proot r 2 ?t] =>
    let T := type of t in
    let p := radcan_reify_term r t (@nil T) in
    lazymatch p with (?e, ?env) =>
      let c := eval vm_compute in (denest_findm e) in
      lazymatch c with
      | Some ?c =>
        let H := fresh "H" in let h := fresh "h" in
        (have H : denest_ok e c by vm_compute);
        have h : proot r 2 t = rinterp r env (dc_rexpr c) :=
          denest_sound r env H;
        rewrite h {h H} /dc_rexpr /=
      end
    end
  end.

Section DenestMulti.
Variables (F : numFieldType) (r : posroot F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

Lemma m1 :
  \sqrt (10 + 2 * \sqrt 6 + 2 * \sqrt 10 + 2 * \sqrt 15) =
  \sqrt 2 + \sqrt 3 + \sqrt 5.
Proof. denest_atm r. radcan. Qed.

Lemma m2 :
  \sqrt (6 + 2 * \sqrt 2 + 2 * \sqrt 3 + 2 * \sqrt 6) =
  1 + \sqrt 2 + \sqrt 3.
Proof. radcan_denest r. Qed.

(* minus signs, rational coefficients *)
Lemma m3 :
  \sqrt (9 + 4 * \sqrt 2 - 4 * \sqrt 3 - 2 * \sqrt 6) =
  2 + \sqrt 2 - \sqrt 3.
Proof. radcan_denest r. Qed.

Lemma m4 :
  \sqrt ((10 + 2 * \sqrt 6 + 2 * \sqrt 10 + 2 * \sqrt 15) / 4)
  = (\sqrt 2 + \sqrt 3 + \sqrt 5) / 2.
Proof. radcan_denest r. Qed.

(* the sign certificate chooses sqrt 11 - sqrt 2 - sqrt 3 >= 0 *)
Lemma m5 :
  \sqrt (16 + 2 * \sqrt 6 - 2 * \sqrt 22 - 2 * \sqrt 33) =
  \sqrt 11 - \sqrt 2 - \sqrt 3.
Proof. radcan_denest r. Qed.

(* four terms, six roots in the radicand *)
Lemma m6 :
  \sqrt (11 + 2 * \sqrt 2 + 2 * \sqrt 3 + 2 * \sqrt 5
         + 2 * \sqrt 6 + 2 * \sqrt 10 + 2 * \sqrt 15) =
  1 + \sqrt 2 + \sqrt 3 + \sqrt 5.
Proof. radcan_denest r. Qed.

(* inside a larger goal, with a phase 1 root *)
Lemma m7 :
  \sqrt (10 + 2 * \sqrt 6 + 2 * \sqrt 10 + 2 * \sqrt 15)
  - \sqrt (5 + 2 * \sqrt 6) = \sqrt 5.
Proof. radcan_denest r. Qed.

(* five terms, ten roots; radcan does it too, through its pre-pass *)
Lemma m8 :
  \sqrt (18 + 2 * \sqrt 2 + 2 * \sqrt 3 + 2 * \sqrt 5
    + 2 * \sqrt 7 + 2 * \sqrt 6 + 2 * \sqrt 10 + 2 * \sqrt 14
    + 2 * \sqrt 15 + 2 * \sqrt 21 + 2 * \sqrt 35) =
  1 + \sqrt 2 + \sqrt 3 + \sqrt 5 + \sqrt 7.
Proof. radcan. Qed.

(* the cross terms 2 sqrt 6, 2 sqrt 10, 3 sqrt 15 come from no candidate:
   the finder fails *)
Goal \sqrt (10 + 2 * \sqrt 6 + 2 * \sqrt 10 + 3 * \sqrt 15)
  = 0.
Proof. Fail denest_atm r. Abort.

(* a wrong right-hand side is refused *)
Goal \sqrt (10 + 2 * \sqrt 6 + 2 * \sqrt 10 + 2 * \sqrt 15)
  = \sqrt 2 + \sqrt 3 - \sqrt 5.
Proof. Fail radcan_denest r. Abort.

End DenestMulti.

(* on a real closed field *)
Lemma rc_denest_multi (R : rcfType) :
  rootR 2 (6 + 2 * rootR 2 2 + 2 * rootR 2 3 + 2 * rootR 2 (6 : R)) =
  1 + rootR 2 2 + rootR 2 3.
Proof. radcan_denest (rootR_posroot R). Qed.

(* Phase 5: several square roots with variables (Denest.v, denest_findvm).
   The radicand is A + sum_j B_j s_j, the s_j distinct products of square
   roots of polynomials (atoms of the coprime square-free basis), A and B_j
   polynomials.  The candidate sum_i c_i w_i has k terms when there are
   k (k - 1) / 2 products s_j (k = 3, 4, 5), the w_i products of atoms, the
   c_i polynomials: c_i c_j = B / (2 g ^ 2) with w_i w_j = g ^ 2 s, B the
   coefficient of s, c_1 ^ 2 = c_1 c_2 * c_1 c_3 / c_2 c_3.  It is checked
   by squaring (radcan_check, its conditions), its sign by nn_conds, or the
   condition 0 <= candidate when the signs are mixed.  radcan does it
   through its pre-pass (phase 3 first, then phase 5) *)

Section DenestMultiVar.
Variables (F : numFieldType) (r : posroot F) (x y z : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

Lemma mv1 (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z) :
  \sqrt (x + y + z + 2 * \sqrt (x * y) + 2 * \sqrt (x * z)
         + 2 * \sqrt (y * z)) = \sqrt x + \sqrt y + \sqrt z.
Proof. radcan. - exact: hz. - exact: hy. - exact: hx. Qed.

Lemma mv2 (hx : 0 <= x) (hy : 0 <= y) :
  \sqrt (x + y + 1 + 2 * \sqrt x + 2 * \sqrt y
         + 2 * \sqrt (x * y)) = 1 + \sqrt x + \sqrt y.
Proof. radcan. - exact: hy. - exact: hx. Qed.

(* roots of polynomials: 0 <= x + 1 is refined away *)
Lemma mv3 (hx : 0 <= x) :
  \sqrt (2 * x + 2 + 2 * \sqrt x + 2 * \sqrt (x + 1)
         + 2 * \sqrt (x * (x + 1))) =
  1 + \sqrt x + \sqrt (x + 1).
Proof. radcan. exact: hx. Qed.

(* a polynomial coefficient: c_1 = x *)
Lemma mv4 (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z) :
  \sqrt (x ^+ 2 + y + z + 2 * x * \sqrt y + 2 * x * \sqrt z
         + 2 * \sqrt (y * z)) = x + \sqrt y + \sqrt z.
Proof. radcan. - exact: hz. - exact: hy. - exact: hx. Qed.

(* mixed signs: the sign of the candidate is a condition *)
Lemma mv5 (hx : 0 <= x) (hy : 0 <= y) (h : 1 <= \sqrt x + \sqrt y) :
  \sqrt (x + y + 1 - 2 * \sqrt x - 2 * \sqrt y
         + 2 * \sqrt (x * y)) = \sqrt x + \sqrt y - 1.
Proof. radcan. - exact: hy. - exact: hx. - exact: h. Qed.

(* four terms, six products of roots *)
Lemma mv6 (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z) :
  \sqrt (x + y + z + 1 + 2 * \sqrt x + 2 * \sqrt y
    + 2 * \sqrt z + 2 * \sqrt (x * y) + 2 * \sqrt (x * z)
    + 2 * \sqrt (y * z)) = 1 + \sqrt x + \sqrt y + \sqrt z.
Proof. radcan. - exact: hz. - exact: hy. - exact: hx. Qed.

(* the cross terms 2, 2, 3 come from no candidate: radcan fails *)
Goal \sqrt (x + y + z + 2 * \sqrt (x * y) + 2 * \sqrt (x * z)
            + 3 * \sqrt (y * z)) =
  \sqrt x + \sqrt y + \sqrt z.
Proof. Fail radcan. Abort.

(* a wrong right-hand side is refused *)
Goal \sqrt (x + y + z + 2 * \sqrt (x * y) + 2 * \sqrt (x * z)
            + 2 * \sqrt (y * z)) =
  \sqrt x + \sqrt y - \sqrt z.
Proof. Fail radcan. Abort.

End DenestMultiVar.

(* on a real closed field *)
Lemma rc_denest_multi_var (R : rcfType) (x y : R) (hx : 0 <= x) (hy : 0 <= y) :
  rootR 2 (x + y + 1 + 2 * rootR 2 x + 2 * rootR 2 y + 2 * rootR 2 (x * y))
  = 1 + rootR 2 x + rootR 2 y.
Proof. radcan. - exact: hy. - exact: hx. Qed.
