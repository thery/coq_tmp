(******************************************************************************)
(* Mono: monomials, their orders and their meaning.                           *)
(*   fct, mono   == radical factor (b, n, e) = proot n b ^+ e, and lists      *)
(*   atom        == variable AVar i, inverse AInv e or root ARoot n e of an   *)
(*                  expression that could not be simplified                   *)
(*   vmono, key  == variable monomial (sorted (atom, exponent)), and the key  *)
(*                  (vmono, mono) of a term coef * vmono * mono               *)
(*   *_cmp       == total orders keeping normal forms sorted                  *)
(*   holds cs    == every condition of cs holds (proof device)                *)
(*   MonoF N     == fct_norm, fct_comb, mono_mul: product of root monomials,  *)
(*                  as an integer coefficient times a reduced monomial        *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition fct := (positive * nat * nat)%type.
Definition mono := seq fct.

Definition fct_cmp (f1 f2 : fct) : comparison :=
  let: (b1, n1, e1) := f1 in
  let: (b2, n2, e2) := f2 in
  match p_cmp b1 b2 with
  | Eq => match Nat.compare n1 n2 with
          | Eq => Nat.compare e1 e2
          | c => c
          end
  | c => c
  end.

Fixpoint mono_cmp (m1 m2 : mono) : comparison :=
  match m1, m2 with
  | [::], [::] => Eq
  | [::], _ => Lt
  | _, [::] => Gt
  | f1 :: m1', f2 :: m2' =>
    match fct_cmp f1 f2 with
    | Eq => mono_cmp m1' m2'
    | c => c
    end
  end.

(* Variables and atoms *)

Inductive atom : Type :=
  | AVar : nat -> atom
  | AInv : rexpr -> atom              (* (rinterp e)^-1 *)
  | ARoot : positive -> rexpr -> atom. (* proot n (rinterp e) *)

(* sorted (atom, exponent > 0) *)
Definition vmono := seq (atom * nat).
Definition key := (vmono * mono)%type.

Definition lex (c1 c2 : comparison) : comparison :=
  if c1 is Eq then c2 else c1.

Definition rtag (e : rexpr) : nat :=
  match e with
  | RCst _ => 0 | RVar _ => 1 | RRoot _ _ => 2 | RAdd _ _ => 3 | ROpp _ => 4
  | RSub _ _ => 5 | RMul _ _ => 6 | RPow _ _ => 7 | RInv _ => 8
  | RRootE _ _ => 9
  end.

Fixpoint rexpr_cmp (e1 e2 : rexpr) : comparison :=
  match e1, e2 with
  | RCst a, RCst b => Z.compare a b
  | RVar i, RVar j => Nat.compare i j
  | RRoot n p, RRoot m q => lex (Pos.compare n m) (Pos.compare p q)
  | RAdd a b, RAdd c d => lex (rexpr_cmp a c) (rexpr_cmp b d)
  | ROpp a, ROpp c => rexpr_cmp a c
  | RSub a b, RSub c d => lex (rexpr_cmp a c) (rexpr_cmp b d)
  | RMul a b, RMul c d => lex (rexpr_cmp a c) (rexpr_cmp b d)
  | RPow a k, RPow c l => lex (rexpr_cmp a c) (Nat.compare k l)
  | RInv a, RInv c => rexpr_cmp a c
  | RRootE n a, RRootE m c => lex (Pos.compare n m) (rexpr_cmp a c)
  | _, _ => Nat.compare (rtag e1) (rtag e2)
  end.

Definition atom_cmp (a1 a2 : atom) : comparison :=
  match a1, a2 with
  | AVar i, AVar j => Nat.compare i j
  | AInv e1, AInv e2 => rexpr_cmp e1 e2
  | ARoot n e1, ARoot m e2 => lex (Pos.compare n m) (rexpr_cmp e1 e2)
  | AVar _, _ => Lt
  | _, AVar _ => Gt
  | AInv _, ARoot _ _ => Lt
  | ARoot _ _, AInv _ => Gt
  end.

Fixpoint vmono_mul (v1 v2 : vmono) {struct v1} : vmono :=
  match v1 with
  | [::] => v2
  | (i1, k1) :: v1' =>
    let fix aux (v2 : vmono) : vmono :=
      match v2 with
      | [::] => v1
      | (i2, k2) :: v2' =>
        match atom_cmp i1 i2 with
        | Lt => (i1, k1) :: vmono_mul v1' v2
        | Gt => (i2, k2) :: aux v2'
        | Eq => (i1, (k1 + k2)%N) :: vmono_mul v1' v2'
        end
      end in aux v2
  end.

Fixpoint vmono_cmp (v1 v2 : vmono) : comparison :=
  match v1, v2 with
  | [::], [::] => Eq
  | [::], _ => Lt
  | _, [::] => Gt
  | (i1, k1) :: v1', (i2, k2) :: v2' =>
    lex (atom_cmp i1 i2) (lex (Nat.compare k1 k2) (vmono_cmp v1' v2'))
  end.

Definition key_cmp (k1 k2 : key) : comparison :=
  lex (vmono_cmp k1.1 k2.1) (mono_cmp k1.2 k2.2).

Definition cmp_eqb (c : comparison) : bool := if c is Eq then true else false.

Definition vsingle (a : atom) (k : nat) : vmono :=
  if k is O then [::] else [:: (a, k)].

Definition cond_cmp (c1 c2 : cond) : comparison :=
  match c1, c2 with
  | CGe0 a, CGe0 b => rexpr_cmp a b
  | CNeq0 a, CNeq0 b => rexpr_cmp a b
  | CGe0 _, CNeq0 _ => Lt
  | CNeq0 _, CGe0 _ => Gt
  end.

Definition cdedup (cs : seq cond) : seq cond :=
  foldr (fun c acc => if has (fun c' => cmp_eqb (cond_cmp c c')) acc then acc
                      else c :: acc) [::] cs.

Local Open Scope ring_scope.

Section MonoSound.

Variable F : numFieldType.
Variable r : posroot F.

(* two identities on powers of roots *)

Lemma proot_exprMn n k e a : (0 < n)%N -> (0 < k)%N -> 0 <= a ->
  proot r (n * k) a ^+ (e * k) = proot r n a ^+ e.
Proof. by move=> n0 k0 a0; rewrite [(e * k)%N]mulnC exprM prootMn. Qed.

Lemma proot_expr_divmod n e a : (0 < n)%N -> 0 <= a ->
  proot r n a ^+ e = a ^+ (e %/ n) * proot r n a ^+ (e %% n).
Proof.
by move=> n0 a0; rewrite {1}(divn_eq e n) exprD mulnC exprM prootK.
Qed.

Definition fct_interp (f : fct) : F :=
  let: (b, n, e) := f in proot r n (pos2F F b) ^+ e.

Definition mono_interp (m : mono) : F := \prod_(f <- m) fct_interp f.

Lemma mono_interp_cons f m :
  mono_interp (f :: m) = fct_interp f * mono_interp m.
Proof. by rewrite /mono_interp big_cons. Qed.

Lemma mono_interp_cat m1 m2 :
  mono_interp (m1 ++ m2) = mono_interp m1 * mono_interp m2.
Proof. by rewrite /mono_interp big_cat. Qed.

Lemma mono_interp_nil : mono_interp [::] = 1.
Proof. by rewrite /mono_interp big_nil. Qed.

Lemma fct_cmp_eq f1 f2 : fct_cmp f1 f2 = Eq -> f1 = f2.
Proof.
case: f1 f2 => [[b1 n1] e1] [[b2 n2] e2] /=.
rewrite /p_cmp; case: Pos.compare_spec => // <-.
case: Nat.compare_spec => // <-.
by case: Nat.compare_spec => // <-.
Qed.

Lemma mono_cmp_eq m1 m2 : mono_cmp m1 m2 = Eq -> m1 = m2.
Proof.
elim: m1 m2 => [|f1 m1 IH] [|f2 m2] //=.
by case E : (fct_cmp f1 f2) => // /IH ->; rewrite (fct_cmp_eq E).
Qed.

(* comparisons *)

Lemma lexP c1 c2 : lex c1 c2 = Eq -> c1 = Eq /\ c2 = Eq.
Proof. by case: c1. Qed.

Lemma rexpr_cmp_eq e1 e2 : rexpr_cmp e1 e2 = Eq -> e1 = e2.
Proof.
elim: e1 e2 =>
  [a|i|n p|n a IHa|a IHa b IHb|a IHa|a IHa b IHb|a IHa b IHb|a IHa k|a IHa]
  [b'|j|m q|m c|c d|c|c d|c d|c l|c] //=.
all: first [ by move/Z.compare_eq ->
           | by case/lexP => /Pos.compare_eq -> /IHa ->
           | by move/Nat.compare_eq ->
           | by case/lexP => /Pos.compare_eq -> /Pos.compare_eq ->
           | by case/lexP => /IHa -> /IHb ->
           | by case/lexP => /IHa -> /Nat.compare_eq ->
           | by move/IHa -> ].
Qed.

Lemma atom_cmp_eq a1 a2 : atom_cmp a1 a2 = Eq -> a1 = a2.
Proof.
case: a1 a2 => [i|e1|n e1] [j|e2|m e2] //=.
- by move/Nat.compare_eq ->.
- by move/rexpr_cmp_eq ->.
by case/lexP => /Pos.compare_eq -> /rexpr_cmp_eq ->.
Qed.

Lemma vmono_cmp_eq v1 v2 : vmono_cmp v1 v2 = Eq -> v1 = v2.
Proof.
elim: v1 v2 => [|[i1 k1] v1 IH] [|[i2 k2] v2] //=.
by case/lexP => /atom_cmp_eq -> /lexP [/Nat.compare_eq -> /IH ->].
Qed.

Lemma key_cmp_eq k1 k2 : key_cmp k1 k2 = Eq -> k1 = k2.
Proof.
case: k1 k2 => [v1 m1] [v2 m2]; rewrite /key_cmp /=.
by case/lexP => /vmono_cmp_eq -> /mono_cmp_eq ->.
Qed.

Lemma cmp_eqbP c : cmp_eqb c -> c = Eq.
Proof. by case: c. Qed.

Lemma exprVpred (x : F) N : (0 < N)%N -> x ^+ N.-1 * (x ^+ N)^-1 = x^-1.
Proof.
move=> N0; rewrite -[in x ^+ N](prednK N0) exprS invfM mulrCA.
have [->|x0] := eqVneq x 0.
  case: N.-1 => [|k]; rewrite ?expr0 ?invr1 ?mulr1 //.
  by rewrite expr0n mul0r invr0 mulr0.
by rewrite divff ?mulr1 // expf_neq0.
Qed.

Variable env : seq F.

Local Notation cond_interp := (cond_interp r env).
Local Notation all_conds := (all_conds r env).

Definition atom_interp (a : atom) : F :=
  match a with
  | AVar i => nth 0 env i
  | AInv e => (rinterp r env e)^-1
  | ARoot n e => proot r (Pos.to_nat n) (rinterp r env e)
  end.

Definition vmono_interp (v : vmono) : F :=
  \prod_(ik <- v) atom_interp ik.1 ^+ ik.2.

Definition key_interp (k : key) : F := vmono_interp k.1 * mono_interp k.2.

Lemma vmono_interp_nil : vmono_interp [::] = 1.
Proof. by rewrite /vmono_interp big_nil. Qed.

Lemma vmono_interp_cons ik v :
  vmono_interp (ik :: v) = atom_interp ik.1 ^+ ik.2 * vmono_interp v.
Proof. by rewrite /vmono_interp big_cons. Qed.

Lemma vmono_mul_sound v1 v2 :
  vmono_interp (vmono_mul v1 v2) = vmono_interp v1 * vmono_interp v2.
Proof.
elim: v1 v2 => [|[i1 k1] v1 IH1] v2 /=; first by rewrite vmono_interp_nil mul1r.
elim: v2 => [|[i2 k2] v2 IH2] /=; first by rewrite vmono_interp_nil mulr1.
case E : (atom_cmp i1 i2).
- by rewrite !vmono_interp_cons IH1 /= (atom_cmp_eq E) exprD mulrACA.
- by rewrite !vmono_interp_cons IH1 vmono_interp_cons mulrA.
by rewrite !vmono_interp_cons IH2 vmono_interp_cons mulrCA.
Qed.

Lemma vsingle_sound a k : vmono_interp (vsingle a k) = atom_interp a ^+ k.
Proof.
case: k => [|k]; first by rewrite /= vmono_interp_nil expr0.
by rewrite /= vmono_interp_cons vmono_interp_nil mulr1.
Qed.

Definition holds (cs : seq cond) : Prop :=
  forall c, List.In c cs -> cond_interp c.

Lemma all_condsP cs : all_conds cs -> holds cs.
Proof.
elim: cs => [|c cs IH] /=; first by move=> _ c [].
case: cs IH => [|c' cs] IH.
  by move=> Hc c0 [<-|].
by case=> Hc /IH Hcs c0 [<-|/Hcs].
Qed.

Lemma holds_cat cs1 cs2 : holds (cs1 ++ cs2) -> holds cs1 /\ holds cs2.
Proof.
by move=> H; split=> c Hc; apply: H; apply: List.in_or_app; [left|right].
Qed.

Lemma holds_cons c cs : holds (c :: cs) -> cond_interp c /\ holds cs.
Proof.
by move=> H; split; [apply: H; left | move=> c' Hc'; apply: H; right].
Qed.

Lemma cond_cmp_eq c1 c2 : cond_cmp c1 c2 = Eq -> c1 = c2.
Proof. by case: c1 c2 => e1 [] e2 //= /rexpr_cmp_eq ->. Qed.

Lemma holds_dedup cs : holds (cdedup cs) -> holds cs.
Proof.
elim: cs => [|c cs IH] //= H.
have Hin : forall l, holds l ->
    has (fun c' => cmp_eqb (cond_cmp c c')) l -> cond_interp c.
  elim=> [|c' l IHl] //= Hl /orP[/cmp_eqbP/cond_cmp_eq ->|].
    by apply: Hl; left.
  by apply: IHl => c0 Hc0; apply: Hl; right.
move: H; case: ifP => Hh H.
  by move=> c0 [<-|/(IH H)] //; exact: Hin Hh.
by case/holds_cons: H => Hc /IH Hcs c0 [<-|/Hcs].
Qed.

End MonoSound.

Section MonoSound0.

Variable F : numFieldType.
Variable rt : nat -> F -> F.
Variable env : seq F.

Local Notation ri := (rinterp_gen rt env).
Local Notation cond_interp_gen := (cond_interp_gen rt env).
Local Notation all_conds_gen := (all_conds_gen rt env).

Definition atom_interp0 (a : atom) : F :=
  match a with
  | AVar i => nth 0 env i
  | AInv e => (ri e)^-1
  | ARoot n e => rt (Pos.to_nat n) (ri e)
  end.

Definition vmono_interp0 (v : vmono) : F :=
  \prod_(ik <- v) atom_interp0 ik.1 ^+ ik.2.

Definition holds0 (cs : seq cond) : Prop :=
  forall c, List.In c cs -> cond_interp_gen c.

Lemma all_conds_genP cs : all_conds_gen cs -> holds0 cs.
Proof.
elim: cs => [|c cs IH] /=; first by move=> _ c [].
case: cs IH => [|c' cs] IH.
  by move=> Hc c0 [<-|].
by case=> Hc /IH Hcs c0 [<-|/Hcs].
Qed.

Lemma holds0_cat cs1 cs2 : holds0 (cs1 ++ cs2) -> holds0 cs1 /\ holds0 cs2.
Proof.
by move=> H; split=> c Hc; apply: H; apply: List.in_or_app; [left|right].
Qed.

Lemma holds0_cons c cs : holds0 (c :: cs) -> cond_interp_gen c /\ holds0 cs.
Proof.
by move=> H; split; [apply: H; left | move=> c' Hc'; apply: H; right].
Qed.

Lemma holds0_dedup cs : holds0 (cdedup cs) -> holds0 cs.
Proof.
elim: cs => [|c cs IH] //= H.
have Hin : forall l, holds0 l ->
    has (fun c' => cmp_eqb (cond_cmp c c')) l -> cond_interp_gen c.
  elim=> [|c' l IHl] //= Hl /orP[/cmp_eqbP/cond_cmp_eq ->|].
    by apply: Hl; left.
  by apply: IHl => c0 Hc0; apply: Hl; right.
move: H; case: ifP => Hh H.
  by move=> c0 [<-|/(IH H)] //; exact: Hin Hh.
by case/holds0_cons: H => Hc /IH Hcs c0 [<-|/Hcs].
Qed.

Lemma vmono_interp0_nil : vmono_interp0 [::] = 1.
Proof. by rewrite /vmono_interp0 big_nil. Qed.

Lemma vmono_interp0_cons ik v :
  vmono_interp0 (ik :: v) = atom_interp0 ik.1 ^+ ik.2 * vmono_interp0 v.
Proof. by rewrite /vmono_interp0 big_cons. Qed.

Lemma vmono_mul_sound0 v1 v2 :
  vmono_interp0 (vmono_mul v1 v2) = vmono_interp0 v1 * vmono_interp0 v2.
Proof.
elim: v1 v2 => [|[i1 k1] v1 IH1] v2 /=.
  by rewrite vmono_interp0_nil mul1r.
elim: v2 => [|[i2 k2] v2 IH2] /=; first by rewrite vmono_interp0_nil mulr1.
case E : (atom_cmp i1 i2).
- by rewrite !vmono_interp0_cons IH1 /= (atom_cmp_eq E) exprD mulrACA.
- by rewrite !vmono_interp0_cons IH1 vmono_interp0_cons mulrA.
by rewrite !vmono_interp0_cons IH2 vmono_interp0_cons mulrCA.
Qed.

End MonoSound0.

(* Products of root monomials (they depend on the number backend) *)

Module MonoF (Import N : NUM).

Include NumFacts N.

(* proot n b ^+ e as a coefficient times a reduced monomial *)
Definition fct_norm (b : positive) (n e : nat) : int * mono :=
  match n with
  | O => (i_one, [:: (b, n, e)])
  | S _ =>
    if p_eqb b xH then (i_one, [::]) else
    let c := i_pow b (e %/ n) in
    let e' := (e %% n)%N in
    if e' == 0%N then (c, [::])
    else let g := gcdn n e' in (c, [:: (b, n %/ g, e' %/ g)]%N)
  end.

(* proot n1 b ^+ e1 * proot n2 b ^+ e2 *)
Definition fct_comb (b : positive) (n1 e1 n2 e2 : nat) : int * mono :=
  if (n1 == 0%N) || (n2 == 0%N) then (i_one, [:: (b, n1, e1); (b, n2, e2)])
  else let l := lcmn n1 n2 in
       fct_norm b l (e1 * (l %/ n1) + e2 * (l %/ n2))%N.

Fixpoint mono_mul (m1 m2 : mono) {struct m1} : int * mono :=
  match m1 with
  | [::] => (i_one, m2)
  | (b1, n1, e1) :: m1' =>
    let fix aux (m2 : mono) : int * mono :=
      match m2 with
      | [::] => (i_one, m1)
      | (b2, n2, e2) :: m2' =>
        match p_cmp b1 b2 with
        | Lt => let: (c, m) := mono_mul m1' m2 in (c, (b1, n1, e1) :: m)
        | Gt => let: (c, m) := aux m2' in (c, (b2, n2, e2) :: m)
        | Eq => let: (c1, m0) := fct_comb b1 n1 e1 n2 e2 in
                let: (c, m) := mono_mul m1' m2' in (i_mul c1 c, m0 ++ m)
        end
      end in aux m2
  end.

Local Open Scope ring_scope.

Section MonoMulSound.

Variable F : numFieldType.
Variable r : posroot F.

Local Notation fct_interp := (fct_interp r).
Local Notation mono_interp := (mono_interp r).

Lemma fct_norm_sound b n e :
  I2F F (fct_norm b n e).1 * mono_interp (fct_norm b n e).2 =
  proot r n (pos2F F b) ^+ e.
Proof.
rewrite /fct_norm /mono_interp; case: n => [|n'].
  by rewrite big_seq1 I2F_i_one mul1r.
set N := n'.+1; have N0 : (0 < N)%N by [].
rewrite /p_eqb; case: Pos.eqb_spec => [->|_].
  by rewrite big_nil I2F_i_one mulr1 /pos2F /= proot_1 // expr1n.
rewrite (proot_expr_divmod r _ N0 (pos2F_ge0 b)).
case: eqP => [e0|e0] /=.
  by rewrite big_nil I2F_i_pow mulr1 e0 expr0 mulr1.
rewrite big_seq1 I2F_i_pow /=; congr (_ * _).
set e' := (e %% N)%N; set g := gcdn N e'.
have g0 : (0 < g)%N by rewrite gcdn_gt0 N0.
have Ng : N = (N %/ g * g)%N by rewrite divnK // dvdn_gcdl.
have eg : e' = (e' %/ g * g)%N by rewrite divnK // dvdn_gcdr.
have Ng0 : (0 < N %/ g)%N by rewrite divn_gt0 // dvdn_leq // dvdn_gcdl.
by rewrite -(proot_exprMn r _ Ng0 g0 (pos2F_ge0 b)) -Ng -eg.
Qed.

Lemma proot_expr_lift n l e a :
  (0 < n)%N -> (0 < l)%N -> (n %| l)%N -> 0 <= a ->
  proot r n a ^+ e = proot r l a ^+ (e * (l %/ n)).
Proof.
move=> n0 l0 nl a0.
have k0 : (0 < l %/ n)%N by rewrite divn_gt0 // dvdn_leq.
by rewrite -(proot_exprMn r _ n0 k0 a0) mulnC divnK.
Qed.

Lemma fct_comb_sound b n1 e1 n2 e2 :
  I2F F (fct_comb b n1 e1 n2 e2).1 * mono_interp (fct_comb b n1 e1 n2 e2).2 =
  proot r n1 (pos2F F b) ^+ e1 * proot r n2 (pos2F F b) ^+ e2.
Proof.
rewrite /fct_comb; case: ifP => [_|].
  by rewrite /mono_interp big_cons big_seq1 I2F_i_one mul1r.
move/negbT; rewrite negb_or -!lt0n => /andP[n10 n20].
have l0 : (0 < lcmn n1 n2)%N by rewrite lcmn_gt0 n10.
rewrite fct_norm_sound exprD.
by rewrite -!proot_expr_lift ?pos2F_ge0 ?dvdn_lcml ?dvdn_lcmr.
Qed.

Lemma mono_mul_sound m1 m2 :
  I2F F (mono_mul m1 m2).1 * mono_interp (mono_mul m1 m2).2 =
  mono_interp m1 * mono_interp m2.
Proof.
elim: m1 m2 => [|[[b1 n1] e1] m1 IH1] m2 /=.
  by rewrite I2F_i_one mul1r mono_interp_nil mul1r.
elim: m2 => [|[[b2 n2] e2] m2 IH2] /=.
  by rewrite I2F_i_one mul1r mono_interp_nil mulr1.
rewrite /p_cmp; case: Pos.compare_spec => [<-|_|_].
- have H1 := fct_comb_sound b1 n1 e1 n2 e2; have H2 := IH1 m2.
  move: H1 H2; case: (fct_comb _ _ _ _ _) => c1 m0.
  case: (mono_mul m1 m2) => c m /= H1 H2.
  rewrite I2F_i_mul mono_interp_cat !mono_interp_cons mulrACA H1 H2 /=.
  by rewrite mulrACA.
- move: (IH1 ((b2, n2, e2) :: m2)); case: (mono_mul _ _) => c m /= H.
  by rewrite (mono_interp_cons r _ m) mulrCA H (mono_interp_cons r _ m1) mulrA.
move: IH2; case: (_ m2) => c m /= H.
by rewrite (mono_interp_cons r _ m) mulrCA H (mono_interp_cons r _ m2) mulrCA.
Qed.

End MonoMulSound.

End MonoF.
