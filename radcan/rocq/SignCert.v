(******************************************************************************)
(* SignCert: sign certificates for constant polynomials in roots.             *)
(*   rt_ok rt   == on 0 <= a and 0 < n, rt n a is nonnegative and is either   *)
(*                 0 or an n-th root of a: true for proot r (posroot_ok) and  *)
(*                 for the root-free reading fun _ _ => 0 (zero_ok)           *)
(*   catom a    == Some (inv, n, p) when a is proot n p (inv = false) or its  *)
(*                 inverse (inv = true), p a positive integer                 *)
(*   abound j a == upper bound of a at precision 2^-j: U / 2^j with           *)
(*                 p * 2^(j n) <= U^n, or 2^j / L with L^n <= p * 2^(j n)     *)
(*   plow j P   == lower bound of P: constant term, 0 for positive terms,     *)
(*                 c * bound of the monomial for negative c                   *)
(*   scert k P  == the fact (k, P) holds, P constant in such atoms, checked   *)
(*                 at the precisions 1, 1/2, ..., 1/2^47                      *)
(*   scert_sound : rt_ok rt -> scert k P -> kI k (peval rt env P)             *)
(* Every atom only uses 0 <= x <= u, valid whether the root is 0 or the true  *)
(* root: positive terms are bounded below by 0, so e.g. 0 <= 3 - 2 * sqrt 2  *)
(* is certified but sqrt 2 != 0 is not (it fails when roots are read as 0).   *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Backend Radcan RefPoly RefCheck.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Root functions covered by the certificates *)

Local Open Scope ring_scope.

Definition rt_ok (F : numFieldType) (rt : nat -> F -> F) : Prop :=
  forall n a, (0 < n)%N -> 0 <= a ->
  0 <= rt n a /\ (rt n a = 0 \/ rt n a ^+ n = a).

Lemma posroot_ok (F : numFieldType) (r : posroot F) : rt_ok (proot r).
Proof.
by move=> n a n0 a0; rewrite proot_ge0 ?prootK //; split=> //; right.
Qed.

Lemma zero_ok (F : numFieldType) : rt_ok (fun _ _ => (0 : F)).
Proof. by move=> n a n0 a0; split=> //; left. Qed.

(* Integer computations *)

Local Close Scope ring_scope.
Local Open Scope Z_scope.

Definition zpow (s : Z) (n : nat) : Z := iter n (Z.mul s) 1.

(* the largest s in [lo, hi) with s ^ n <= N, if lo ^ n <= N < hi ^ n *)
Fixpoint zbis (fuel n : nat) (N lo hi : Z) : Z :=
  match fuel with
  | O => lo
  | S f =>
    if Z.leb (Z.sub hi lo) 1 then lo
    else let m := Z.div (Z.add lo hi) 2 in
         if Z.leb (zpow m n) N then zbis f n N m hi else zbis f n N lo m
  end.

Definition ziroot (n : nat) (N : Z) : Z :=
  let k := Z.to_nat (Z.div (Z.log2 N) (Z.of_nat n)) in
  zbis (k.+2) n N 0 (Z.shiftl 1 (Z.of_nat k.+1)).

Definition dpow (j : nat) : positive := iter j xO xH.

Definition catom (a : rexpr) : option (bool * positive * positive) :=
  match a with
  | RRoot n p | RRootE n (RCst (Zpos p)) => Some (false, n, p)
  | RInv (RRoot n p) | RInv (RRootE n (RCst (Zpos p))) => Some (true, n, p)
  | _ => None
  end.

Local Close Scope Z_scope.
Local Open Scope Q_scope.

Definition abound (j : nat) (a : rexpr) : option Q :=
  if catom a is Some (inv, n, p) then
    let k := Pos.to_nat n in
    let D := dpow j in
    let N := Z.mul (Zpos p) (zpow (Zpos D) k) in
    let s := ziroot k N in
    if inv then
      (if Z.ltb 0 s && Z.leb (zpow s k) N then
         Some (Qmake (Zpos D) (Z.to_pos s))
       else None)
    else
      let u := if Z.eqb (zpow s k) N then s else Z.succ s in
      if Z.leb 0 u && Z.leb N (zpow u k) then Some (Qmake u D) else None
  else None.

Definition qpow (b : Q) (k : nat) : Q := iter k (fun c => Qred (b * c)) 1.

Definition mbound (j : nat) (m : amono) : option Q :=
  foldr (fun ak acc =>
           match abound j ak.1, acc with
           | Some b, Some c => Some (Qred (qpow b ak.2 * c))
           | _, _ => None
           end) (Some 1) m.

Definition tlow (j : nat) (t : Q * amono) : option Q :=
  if t.2 is [::] then Some t.1 else
  if mbound j t.2 is Some u then
    Some (if Qle_bool 0 t.1 then 0 else Qred (t.1 * u))
  else None.

Definition plow (j : nat) (P : poly) : option Q :=
  foldr (fun t acc =>
           match tlow j t, acc with
           | Some b, Some c => Some (Qred (b + c))
           | _, _ => None
           end) (Some 0) P.

Definition scheck (j : nat) (k : fkind) (P : poly) : bool :=
  let pos P := if plow j P is Some l then qlt 0 l else false in
  match k with
  | KGe => if plow j P is Some l then Qle_bool 0 l else false
  | KGt => pos P
  | KNe => pos P || pos (pscale (-1) P)
  end.

Definition scert (k : fkind) (P : poly) : bool :=
  if plow 0 P is Some _ then has (fun j => scheck j k P) (iota 0 48)
  else false.

Local Close Scope Q_scope.
Local Open Scope ring_scope.

(* Soundness *)

Section SignCertProofs.
Variable F : numFieldType.

Local Arguments Qred : simpl never.
Local Arguments Qplus : simpl never.
Local Arguments Qmult : simpl never.

Lemma Z2F_ge0z z : Z.le 0 z -> 0 <= Z2F F z.
Proof. by case: z => //= p _; exact: pos2F_ge0. Qed.

Lemma Z2F_lez x y : Z.le x y -> Z2F F x <= Z2F F y.
Proof.
move=> xy; have -> : y = Z.add x (Z.sub y x) by lia.
by rewrite Z2F_add lerDl Z2F_ge0z //; lia.
Qed.

Lemma Z2F_gt0z z : Z.lt 0 z -> 0 < Z2F F z.
Proof.
case: z => //= p _; rewrite lt_def pos2F_ge0 andbT.
exact: pos2F_neq0.
Qed.

Lemma zpowE s n : Z2F F (zpow s n) = Z2F F s ^+ n.
Proof.
elim: n => [|n IH]; first by rewrite expr0 /= pos2F1.
by rewrite /zpow iterS -/(zpow s n) Z2F_mul IH exprS.
Qed.

Lemma qpowE b k : Q2F (F:=F) (qpow b k) = Q2F b ^+ k.
Proof.
elim: k => [|k IH]; first by rewrite Q2F1.
by rewrite /qpow iterS -/(qpow b k) Q2F_red Q2F_mult IH exprS.
Qed.

Lemma Q2F_make z d : Q2F (F:=F) (Qmake z d) = Z2F F z / Z2F F (Zpos d).
Proof. by []. Qed.

Variables (rt : nat -> F -> F) (env : seq F).
Hypothesis Hrt : rt_ok rt.
Local Notation ri := (rinterp_gen rt env).
Local Notation aeval := (aeval rt env).
Local Notation peval := (peval rt env).

(* the value of a recognised atom *)
Lemma catomE a inv n p : catom a = Some (inv, n, p) ->
  ri a = (if inv then (rt (Pos.to_nat n) (pos2F F p))^-1
          else rt (Pos.to_nat n) (pos2F F p)).
Proof.
case: a => //= [n' p' [<- <- <-]|n' [] // [] // p' [<- <- <-]|] //.
by case=> // [n' p' [<- <- <-]|n' [] // [] // p' [<- <- <-]].
Qed.

Lemma root_bound n p : let s := rt (Pos.to_nat n) (pos2F F p) in
  0 <= s /\ (s = 0 \/ s ^+ Pos.to_nat n = pos2F F p).
Proof.
by apply: Hrt; [apply/ssrnat.ltP; exact: Pos2Nat.is_pos|exact: pos2F_ge0].
Qed.

Lemma abound_sound j a b : abound j a = Some b -> 0 <= ri a <= Q2F b.
Proof.
rewrite /abound; case E : (catom a) => [[[inv n] p]|] //; rewrite (catomE E).
set k := Pos.to_nat n; set D := dpow j.
set N := Z.mul _ _; set s := ziroot k N.
have k0 : (0 < k)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
have [s0 hs] := root_bound n p; rewrite -/k in s0 hs.
have D0 : 0 < Z2F F (Zpos D) by exact: Z2F_gt0z.
have NE : Z2F F N = pos2F F p * Z2F F (Zpos D) ^+ k by rewrite Z2F_mul zpowE.
clear E; case: inv.
  case: (Z.ltb_spec 0 s) => //= sp; case: (Z.leb_spec (zpow s k) N) => //.
  move=> sN [<-]; rewrite invr_ge0 s0 /= Q2F_make.
  have -> : Z2F F (Zpos (Z.to_pos s)) = Z2F F s by rewrite Z2Pos.id.
  case: hs => [->|hs]; first by rewrite invr0 divr_ge0 ?ltW // Z2F_gt0z.
  have sp' : 0 < Z2F F s by exact: Z2F_gt0z.
  have s0' : 0 < rt k (pos2F F p).
    rewrite lt_def s0 andbT; apply/eqP => h.
    move: hs; rewrite h expr0n gtn_eqF // => /eqP.
    by rewrite eq_sym (negbTE (pos2F_neq0 _)).
  rewrite -invf_div lef_pV2 ?posrE ?divr_gt0 //.
  have sD : 0 <= Z2F F s / Z2F F (Zpos D) by rewrite divr_ge0 // ltW.
  rewrite -(ler_pXn2r k0) ?nnegrE // hs expr_div_n.
  rewrite ler_pdivrMr ?exprn_gt0 // -NE -zpowE; exact: Z2F_lez.
set u := if Z.eqb _ _ then _ else _.
case: (Z.leb_spec 0 u) => //= u0; case: (Z.leb_spec N (zpow u k)) => //.
move=> Nu [<-]; rewrite s0 /= Q2F_make.
have uD : 0 <= Z2F F u / Z2F F (Zpos D) by rewrite divr_ge0 ?Z2F_ge0z // ltW.
case: hs => [->|hs] //; rewrite -(ler_pXn2r k0) ?nnegrE //.
rewrite hs expr_div_n ler_pdivlMr ?exprn_gt0 // -NE -zpowE; exact: Z2F_lez.
Qed.

Lemma mbound_sound j m u : mbound j m = Some u -> 0 <= aeval m <= Q2F u.
Proof.
elim: m u => [|[a k] m IH] u /=; first by case=> <-; rewrite Q2F1 ler01 lexx.
case Ea : (abound j a) => [b|] //; case Em : (mbound j m) => [c|] // [<-].
have /andP [a0 ab] := abound_sound Ea; have /andP [m0 mc] := IH _ Em.
rewrite Q2F_red Q2F_mult qpowE mulr_ge0 ?exprn_ge0 //=.
rewrite ler_pM ?exprn_ge0 // lerXn2r // ?nnegrE //.
exact: le_trans ab.
Qed.

Lemma tlow_sound j t l : tlow j t = Some l -> Q2F l <= Q2F t.1 * aeval t.2.
Proof.
case: t => q [|ak m] /=; first by rewrite /tlow /= => -[<-]; rewrite mulr1.
have -> : tlow j (q, ak :: m) = if mbound j (ak :: m) is Some u then
    Some (if Qle_bool (Qmake Z0 xH) q then Qmake Z0 xH else Qred (Qmult q u))
    else None by [].
rewrite -[_ * aeval m]/(aeval (ak :: m)).
case E : (mbound j (ak :: m)) => [u|] // [<-].
have /andP [m0 mu] := mbound_sound E.
case: ifP => [/(@Q2F_ge0b F) q0|q0]; first by rewrite Q2F0 mulr_ge0.
have q0' : Q2F (F:=F) q <= 0.
  apply: Q2F_le0b; apply/Qle_bool_iff/Qlt_le_weak/Qnot_le_lt => h.
  by move: q0; rewrite (proj2 (Qle_bool_iff _ _) h).
by rewrite Q2F_red Q2F_mult ler_wnM2l.
Qed.

Lemma plow_sound j P l : plow j P = Some l -> Q2F l <= peval P.
Proof.
elim: P l => [|t P IH] l /=; first by case=> <-; rewrite Q2F0.
case Et : (tlow j t) => [b|] //; case EP : (plow j P) => [c|] // [<-].
by rewrite Q2F_red Q2F_plus lerD // ?(tlow_sound Et) ?IH.
Qed.

Lemma scheck_sound j k P : scheck j k P -> kI k (peval P).
Proof.
have pos Q : (if plow j Q is Some l then qlt 0 l else false) -> 0 < peval Q.
  case E : (plow j Q) => [l|] // /(@Q2F_gt0b F) l0.
  exact: lt_le_trans l0 (plow_sound E).
case: k => /=.
- case E : (plow j P) => [l|] // /(@Q2F_ge0b F) l0.
  exact: le_trans l0 (plow_sound E).
- exact: pos.
case/orP => /pos; first exact: lt0r_neq0.
by rewrite pscale_sound Q2Fm1 mulN1r oppr_gt0 => /ltr0_neq0.
Qed.

Theorem scert_sound k P : scert k P -> kI k (peval P).
Proof.
rewrite /scert; case: (plow 0 P) => // _ /hasP [j _].
exact: scheck_sound.
Qed.

End SignCertProofs.
