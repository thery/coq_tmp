(******************************************************************************)
(* RefPoly: the data of the refinement and polynomials over atoms.            *)
(*   bound      == (neg, n, d), the number -(n/d) if neg, n/d otherwise       *)
(*   amono      == product of powers of atoms (any rexpr read as a value)     *)
(*   side       == sum of terms c * m, shown as x + 2 * y - 1                 *)
(*   rc B       == refined conditions with bounds in B:                       *)
(*     RRaw c       raw condition c : cond                                    *)
(*     RLow s b i   b <= x_i (s = false) or b < x_i (s = true)                *)
(*     RUpp s b i   x_i <= b or x_i < b                                       *)
(*     RInt s1 b1 i s2 b2   b1 <= x_i <= b2 (strict on side k if sk)          *)
(*     RNeq i b     x_i != b                                                  *)
(*     RCmp s l r   l <= r or l < r (l r : side)                              *)
(*     RDiff l r    l != r                                                    *)
(*   rcond      == rc bound                                                   *)
(*   poly       == sparse polynomials over atoms over Q (pnorm e)             *)
(*   peval rt env p == the value of p;  pnorm_sound : peval (pnorm e) = e     *)
(*   lrel P R   == Some (a, b) when P = a * R + b (lrel_sound)                *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Refined conditions *)

Definition bound := (bool * nat * nat)%type.
Definition amono := seq (rexpr * nat).
Definition side := seq (bound * amono).

Inductive rc (B : Type) : Type :=
  | RRaw : cond -> rc B
  | RLow : bool -> B -> nat -> rc B
  | RUpp : bool -> B -> nat -> rc B
  | RInt : bool -> B -> nat -> bool -> B -> rc B
  | RNeq : nat -> B -> rc B
  | RCmp : bool -> side -> side -> rc B
  | RDiff : side -> side -> rc B.

Arguments RRaw {B} c.
Arguments RLow {B} s b i.
Arguments RUpp {B} s b i.
Arguments RInt {B} s1 b1 i s2 b2.
Arguments RNeq {B} i b.
Arguments RCmp {B} s l r.
Arguments RDiff {B} l r.

Definition rcond := rc bound.

(* Polynomials over atoms *)

Local Open Scope Q_scope.

Definition qz (a : Q) : bool := Qeq_bool a 0.
Definition qlt (a b : Q) : bool := ~~ Qle_bool b a.

Definition poly := seq (Q * amono).

Fixpoint amono_cmp (m1 m2 : amono) : comparison :=
  match m1, m2 with
  | [::], [::] => Eq
  | [::], _ => Lt
  | _, [::] => Gt
  | (a1, k1) :: m1', (a2, k2) :: m2' =>
    lex (rexpr_cmp a1 a2) (lex (Nat.compare k1 k2) (amono_cmp m1' m2'))
  end.

Fixpoint amono_mul (m1 m2 : amono) {struct m1} : amono :=
  match m1 with
  | [::] => m2
  | (a1, k1) :: m1' =>
    let fix aux (m2 : amono) : amono :=
      match m2 with
      | [::] => m1
      | (a2, k2) :: m2' =>
        match rexpr_cmp a1 a2 with
        | Lt => (a1, k1) :: amono_mul m1' m2
        | Gt => (a2, k2) :: aux m2'
        | Eq => (a1, (k1 + k2)%N) :: amono_mul m1' m2'
        end
      end in aux m2
  end.

Fixpoint padd (p1 p2 : poly) {struct p1} : poly :=
  match p1 with
  | [::] => p2
  | (c1, m1) :: p1' =>
    let fix aux (p2 : poly) : poly :=
      match p2 with
      | [::] => p1
      | (c2, m2) :: p2' =>
        match amono_cmp m1 m2 with
        | Lt => (c1, m1) :: padd p1' p2
        | Gt => (c2, m2) :: aux p2'
        | Eq => let c := Qred (c1 + c2) in
                if qz c then padd p1' p2' else (c, m1) :: padd p1' p2'
        end
      end in aux p2
  end.

Definition psingle (c : Q) (m : amono) : poly :=
  if qz c then [::] else [:: (c, m)].
Definition pconst (c : Q) : poly := psingle c [::].
Definition patom (a : rexpr) : poly := [:: (1, [:: (a, 1%N)])].

Definition pscale (a : Q) (p : poly) : poly :=
  if qz a then [::] else map (fun t => (Qred (a * t.1), t.2)) p.

Definition pmul_t (t : Q * amono) (q : poly) : poly :=
  foldr (fun u acc => padd (psingle (Qred (t.1 * u.1)) (amono_mul t.2 u.2)) acc)
        [::] q.

Definition pmul (p q : poly) : poly :=
  foldr (fun t acc => padd (pmul_t t q) acc) [::] p.

Definition ppow (p : poly) (k : nat) : poly := iter k (pmul p) (pconst 1).

Fixpoint pnorm (e : rexpr) : poly :=
  match e with
  | RCst z => pconst (Qmake z xH)
  | RAdd a b => padd (pnorm a) (pnorm b)
  | ROpp a => pscale (-1) (pnorm a)
  | RSub a b => padd (pnorm a) (pscale (-1) (pnorm b))
  | RMul a b => pmul (pnorm a) (pnorm b)
  | RPow a k => ppow (pnorm a) k
  | RInv a =>
    match pnorm a with
    | [::] => [::]
    | [:: (c, [::])] => pconst (Qred (Qinv c))
    | _ => patom (RInv a)
    end
  | _ => patom e
  end.

Fixpoint peqb (p q : poly) : bool :=
  match p, q with
  | [::], [::] => true
  | (c1, m1) :: p', (c2, m2) :: q' =>
    Qeq_bool c1 c2 && cmp_eqb (amono_cmp m1 m2) && peqb p' q'
  | _, _ => false
  end.

(* the constant term (always first) and the non-constant part *)
Definition pconst_of (p : poly) : Q := if p is (c, [::]) :: _ then c else 0.
Definition pnc (p : poly) : poly := if p is (_, [::]) :: p' then p' else p.

(* Some (a, b) when P = a * Q + b *)
Definition lrel (P R : poly) : option (Q * Q) :=
  match pnc R, pnc P with
  | (q, _) :: _, (p, _) :: _ =>
    let a := Qred (p / q) in
    let b := Qred (pconst_of P - a * pconst_of R) in
    if peqb P (padd (pscale a R) (pconst b)) then Some (a, b) else None
  | _, _ => None
  end.

Local Close Scope Q_scope.
Local Open Scope ring_scope.

(* Soundness of the polynomials *)

Section PolyProofs.
Variable F : numFieldType.

Local Arguments Qred : simpl never.
Local Arguments Qplus : simpl never.
Local Arguments Qmult : simpl never.
Local Arguments Qopp : simpl never.
Local Arguments Qinv : simpl never.

Lemma Z2F_ge0 z : Z.le 0 z -> 0 <= Z2F F z.
Proof. by case: z => //= p _; exact: pos2F_ge0. Qed.

Lemma pos2F_gt0 p : 0 < pos2F F p.
Proof. by rewrite lt_def pos2F_neq0 pos2F_ge0. Qed.

Lemma Q2F_ge0 q : Qle 0 q -> 0 <= Q2F (F:=F) q.
Proof.
case: q => n d; rewrite /Qle /Q2F /= Z.mul_1_r => H.
by rewrite divr_ge0 ?pos2F_ge0 ?Z2F_ge0.
Qed.

Lemma Z2F_gt0 z : Z.lt 0 z -> 0 < Z2F F z.
Proof. by case: z => //= p _; exact: pos2F_gt0. Qed.

Lemma Q2F_gt0 q : Qlt 0 q -> 0 < Q2F (F:=F) q.
Proof.
case: q => n d; rewrite /Qlt /Q2F /= Z.mul_1_r => H.
by rewrite divr_gt0 ?pos2F_gt0 ?Z2F_gt0.
Qed.

Lemma Q2F_minus a b : Q2F (F:=F) (Qminus b a) = Q2F b - Q2F a.
Proof. by rewrite /Qminus Q2F_plus Q2F_opp. Qed.

Lemma Q2F_le a b : Qle_bool a b -> Q2F (F:=F) a <= Q2F b.
Proof.
move/Qle_bool_iff => H; rewrite -subr_ge0 -Q2F_minus; apply: Q2F_ge0.
by rewrite -(Qplus_opp_r a); apply: Qplus_le_compat => //; exact: Qle_refl.
Qed.

Lemma Q2F_lt a b : qlt a b -> Q2F (F:=F) a < Q2F b.
Proof.
rewrite /qlt => /negP H.
have {}H : Qlt a b by apply: Qnot_le_lt => /Qle_bool_iff.
rewrite -subr_gt0 -Q2F_minus; apply: Q2F_gt0.
by rewrite -(Qplus_opp_r a); apply: Qplus_lt_le_compat => //; exact: Qle_refl.
Qed.

Lemma Q2F_eqb a b : Qeq_bool a b -> Q2F (F:=F) a = Q2F b.
Proof. by move/Qeq_bool_iff; exact: Q2F_Qeq. Qed.

Lemma Q2F0 : Q2F (F:=F) 0 = 0.
Proof. by rewrite /Q2F /= mul0r. Qed.

Lemma Q2F1 : Q2F (F:=F) 1 = 1.
Proof. by rewrite /Q2F /= pos2F1 divr1. Qed.

Lemma Q2Fm1 : Q2F (F:=F) (Qmake (Zneg xH) xH) = -1.
Proof. by rewrite /Q2F /= pos2F1 divr1. Qed.

Lemma qzP a : qz a -> Q2F (F:=F) a = 0.
Proof. by move/Q2F_eqb ->; rewrite Q2F0. Qed.

Lemma Q2F_eq0 b : Q2F (F:=F) b = 0 -> qz b.
Proof.
case: b => [[|n|n] d]; rewrite /qz /Q2F /= => /eqP; rewrite ?mul0r //.
  by rewrite mulf_eq0 invr_eq0 !(negbTE (pos2F_neq0 _)).
by rewrite mulf_eq0 invr_eq0 oppr_eq0 !(negbTE (pos2F_neq0 _)).
Qed.

Lemma Q2F_neq0 a : ~~ qz a -> Q2F (F:=F) a != 0.
Proof. by apply: contra => /eqP /Q2F_eq0. Qed.

Lemma Q2F_gt0b a : qlt 0 a -> 0 < Q2F (F:=F) a.
Proof. by move/Q2F_lt; rewrite Q2F0. Qed.

Lemma Q2F_lt0b a : qlt a 0 -> Q2F (F:=F) a < 0.
Proof. by move/Q2F_lt; rewrite Q2F0. Qed.

Lemma Q2F_ge0b a : Qle_bool 0 a -> 0 <= Q2F (F:=F) a.
Proof. by move/Q2F_le; rewrite Q2F0. Qed.

Lemma Q2F_le0b a : Qle_bool a 0 -> Q2F (F:=F) a <= 0.
Proof. by move/Q2F_le; rewrite Q2F0. Qed.

Variables (rt : nat -> F -> F) (env : seq F).
Local Notation ri := (rinterp_gen rt env).

Definition aeval (m : amono) : F :=
  foldr (fun ak acc => ri ak.1 ^+ ak.2 * acc) 1 m.
Definition peval (p : poly) : F :=
  foldr (fun t acc => Q2F t.1 * aeval t.2 + acc) 0 p.

Lemma amono_cmp_eq m1 m2 : amono_cmp m1 m2 = Eq -> m1 = m2.
Proof.
elim: m1 m2 => [|[a1 k1] m1 IH] [|[a2 k2] m2] //=.
by case/lexP => /rexpr_cmp_eq -> /lexP [/Nat.compare_eq -> /IH ->].
Qed.

Lemma amono_mul_sound m1 m2 : aeval (amono_mul m1 m2) = aeval m1 * aeval m2.
Proof.
elim: m1 m2 => [|[a1 k1] m1 IH1] m2 /=; first by rewrite mul1r.
elim: m2 => [|[a2 k2] m2 IH2] /=; first by rewrite mulr1.
case E : (rexpr_cmp a1 a2) => /=.
- by rewrite IH1 (rexpr_cmp_eq E) exprD mulrACA.
- by rewrite IH1 /= mulrA.
by rewrite IH2 /= mulrCA.
Qed.

Lemma padd_sound p1 p2 : peval (padd p1 p2) = peval p1 + peval p2.
Proof.
elim: p1 p2 => [|[c1 m1] p1 IH1] p2 /=; first by rewrite add0r.
elim: p2 => [|[c2 m2] p2 IH2] /=; first by rewrite addr0.
case E : (amono_cmp m1 m2).
- rewrite -(amono_cmp_eq E); case: ifP => [/qzP|_] /=.
    rewrite Q2F_red Q2F_plus IH1 => H.
    by rewrite addrACA -mulrDl H mul0r add0r.
  by rewrite IH1 Q2F_red Q2F_plus mulrDl addrACA.
- by rewrite /= IH1 /= addrA.
by rewrite /= IH2 /= addrCA.
Qed.

Lemma psingle_sound c m : peval (psingle c m) = Q2F c * aeval m.
Proof.
by rewrite /psingle; case: ifP => [/qzP -> | _] /=; rewrite ?mul0r ?addr0.
Qed.

Lemma pconst_sound c : peval (pconst c) = Q2F c.
Proof. by rewrite psingle_sound /= mulr1. Qed.

Lemma patom_sound a : peval (patom a) = ri a.
Proof. by rewrite /= Q2F1 mul1r expr1 mulr1 addr0. Qed.

Lemma pscale_sound a p : peval (pscale a p) = Q2F a * peval p.
Proof.
rewrite /pscale; case: ifP => [/qzP -> | _] /=; first by rewrite mul0r.
elim: p => [|[c m] p IH] /=; first by rewrite mulr0.
by rewrite IH Q2F_red Q2F_mult mulrDr mulrA.
Qed.

Lemma pmul_t_sound t q : peval (pmul_t t q) = Q2F t.1 * aeval t.2 * peval q.
Proof.
case: t => c m; elim: q => [|[c2 m2] q IH] /=; first by rewrite mulr0.
rewrite padd_sound psingle_sound IH Q2F_red Q2F_mult amono_mul_sound /=.
by rewrite mulrDr; congr (_ + _); rewrite mulrACA.
Qed.

Lemma pmul_sound p q : peval (pmul p q) = peval p * peval q.
Proof.
elim: p => [|t p IH] /=; first by rewrite mul0r.
by rewrite padd_sound pmul_t_sound IH mulrDl.
Qed.

Lemma ppow_sound p k : peval (ppow p k) = peval p ^+ k.
Proof.
elim: k => [|k IH].
  by rewrite expr0 -[ppow p 0]/(pconst 1) pconst_sound Q2F1.
by rewrite /ppow iterS -/(ppow p k) pmul_sound IH exprS.
Qed.

Lemma pnorm_sound e : peval (pnorm e) = ri e.
Proof.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|
            e1 IH1 k|e1 IH1] /=.
- by rewrite pconst_sound Q2F_Z.
- by rewrite Q2F1 mul1r expr1 mulr1 addr0.
- by rewrite Q2F1 mul1r expr1 mulr1 addr0.
- by rewrite Q2F1 mul1r expr1 mulr1 addr0.
- by rewrite padd_sound IH1 IH2.
- by rewrite pscale_sound IH1 Q2Fm1 mulN1r.
- by rewrite padd_sound pscale_sound IH1 IH2 Q2Fm1 mulN1r.
- by rewrite pmul_sound IH1 IH2.
- by rewrite ppow_sound IH1.
move: IH1; case: (pnorm e1) => [|[c [|a m]] [|t p]] /= <-;
  rewrite ?Q2F1 ?mul1r ?expr1 ?mulr1 ?addr0 //.
- by rewrite invr0.
by rewrite pconst_sound Q2F_red Q2F_Qinv.
Qed.

Lemma peqb_sound p q : peqb p q -> peval p = peval q.
Proof.
elim: p q => [|[c1 m1] p IH] [|[c2 m2] q] //=.
by case/andP => /andP [/Q2F_eqb -> /cmp_eqbP /amono_cmp_eq ->] /IH ->.
Qed.

Lemma pconst_ofE p : peval p = Q2F (pconst_of p) + peval (pnc p).
Proof.
case: p => [|[c [|a m]] p] /=; rewrite ?Q2F0 ?add0r //.
by rewrite mulr1.
Qed.

Lemma lrel_sound P R a b : lrel P R = Some (a, b) ->
  peval P = Q2F a * peval R + Q2F b.
Proof.
rewrite /lrel; case: (pnc R) => [|[q m] ?] //; case: (pnc P) => [|[p m'] ?] //.
case: ifP => // /peqb_sound -> [<- <-].
by rewrite padd_sound pscale_sound pconst_sound.
Qed.

End PolyProofs.
