(******************************************************************************)
(* ExpLogTac: explog, equalities on the reals of Stdlib with exp and ln.     *)
(* Generic procedure of Theorem 5.7 of Epstein-Caviness (TR223), see         *)
(* plans/EXPLOG_PLAN.md.  A user file only needs                             *)
(*   From RadcanExpLog Require Import ExpLogTac.                              *)
(* (Reals, Lra, mathcomp, radcan with the canonical structures of Rstruct,   *)
(* and radcan_trig are exported).                                            *)
(*                                                                            *)
(*   explog == unfold tanh, cosh, sinh, Rpower, Rlog, tan; [heuristic H3];  *)
(*             the core: repeat (exp pass; ln pass) until the goal does not  *)
(*             change [with heuristic H5]; [heuristic H4]; zero test (radcan_trig if cos, sin   *)
(*             or tan occur, else radcan_lra) [retried by heuristic H1];      *)
(*             easy conditions are closed, the others are given back after   *)
(*             the main goal, in the order they were met (heuristic H2       *)
(*             drops the conditions implied by the context or the others)    *)
(*   explog_norm == the same without the zero test (shows the normal form)   *)
(* Conditions are hypotheses hc of the main goal; their proofs are          *)
(* collected in one shelved goal Bag (c_1 /\ ... /\ c_n) (see bag_add).       *)
(*                                                                            *)
(* Core, exp pass (Theorem 5.7(b)), one level at a time (innermost first):   *)
(*   the arguments A_1 ... A_k of the exp terms of the level are reified as  *)
(*   rational functions of the atoms (variables, roots, ln terms = ln        *)
(*   letters, exp terms of lower levels); exact Gaussian elimination over Q  *)
(*   ([elim]) on the coefficient vectors of 1, the ln letters and the A_j    *)
(*   gives every dependent A_j as  c + sum r_i l_i + sum s_b A_b; letters    *)
(*   exp (A_b / d_b), exp (1 / d), exp (l_i / q) = q-th root ([eplan]);      *)
(*   each relation is checked by field ([exp_lsumE]).                        *)
(* Core, ln pass (Theorem 5.7(a)), innermost ln first:                        *)
(*   ln A = ln |A| under 0 < A; A is factored (unverified MFactorEEZ) into   *)
(*   +/- prod q^k prod p_i^e_i (q primes, p_i irreducible primitive), the    *)
(*   factorisation is checked by field, and ln |A| = sum k ln q +            *)
(*   sum e_i ln |p_i| under p_i <> 0 ([lnabs_fact]); ln |exp B| = B.         *)
(* ln letters are atoms for the exp pass, exp letters atoms for the ln pass. *)
(* The searches are computed (vm_compute) and not proved; every rewrite is   *)
(* an equality proved in Rocq.                                                *)
(******************************************************************************)
From Stdlib Require Export Reals Lra.
From Stdlib Require Import QArith.
From mathcomp Require Export all_boot all_order all_algebra.
From Radcan Require Export Rstruct PosRoot PosRootFacts RootR RealRoot.
From Radcan Require Export Syntax Radcan Refine Tactic RootRstd.
From RadcanTrig Require Export TrigTac.
From Radcan Require MFactor MFactorEEZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* The searches (unverified)                                                 *)
(* ========================================================================= *)

(* rational expressions over numbered atoms (input of both searches) *)
Inductive re : Type :=
  | RVar of nat | RCst of BinNums.Z
  | RAdd of re & re | RSub of re & re | RMul of re & re | RDiv of re & re
  | ROpp of re | RInv of re | RPow of re & nat.

(* ------------------------------------------------------------------------- *)
(* exp side: Gaussian elimination over Q                                     *)
(* ------------------------------------------------------------------------- *)

(* letters: exp of  1 / d,  atom i / q  (atom i is ln a),  arg b / d *)
Inductive lref : Type :=
  | LOne of positive | LLn of nat & positive | LExp of nat & positive.

Section SearchExp.
Import MFactor.

Definition rf := (mpoly * mpoly)%type.

Definition rf_add (x y : rf) : rf :=
  if meqb x.2 y.2 then (madd x.1 y.1, x.2)
  else (madd (mmul x.1 y.2) (mmul y.1 x.2), mmul x.2 y.2).
Definition rf_opp (x : rf) : rf := (mopp x.1, x.2).
Definition rf_mul (x y : rf) : rf := (mmul x.1 y.1, mmul x.2 y.2).
Definition rf_inv (x : rf) : rf := (x.2, x.1).
Definition rf_pow (x : rf) n : rf := (mpow x.1 n, mpow x.2 n).

Fixpoint re2rf (e : re) : rf :=
  match e with
  | RVar i => (mvar i, mone)
  | RCst c => (mconst c, mone)
  | RAdd a b => rf_add (re2rf a) (re2rf b)
  | RSub a b => rf_add (re2rf a) (rf_opp (re2rf b))
  | RMul a b => rf_mul (re2rf a) (re2rf b)
  | RDiv a b => rf_mul (re2rf a) (rf_inv (re2rf b))
  | ROpp a => rf_opp (re2rf a)
  | RInv a => rf_inv (re2rf a)
  | RPow a n => rf_pow (re2rf a) n
  end.

(* sparse vectors over Q (Stdlib QArith) *)
Notation QQ := QArith_base.Q.
Definition q0 : QQ := Qmake 0 1.
Definition q1 : QQ := Qmake 1 1.

Section Vec.
Variables (K : Type) (keq : K -> K -> bool).

Definition qvec := seq (K * QQ).

Fixpoint vget (k : K) (v : qvec) : QQ :=
  if v is (k', c) :: v' then if keq k k' then c else vget k v' else q0.

Fixpoint vupd (k : K) (c : QQ) (v : qvec) : qvec :=
  match v with
  | [::] => if Qeq_bool c q0 then [::] else [:: (k, c)]
  | (k', c') :: v' =>
    if keq k k' then
      let s := Qred (Qplus c c') in
      if Qeq_bool s q0 then v' else (k', s) :: v'
    else (k', c') :: vupd k c v'
  end.

(* v + a w *)
Definition vaxpy (a : QQ) (w v : qvec) : qvec :=
  foldl (fun v kc => vupd kc.1 (Qred (Qmult a kc.2)) v) v w.

Definition vscale (a : QQ) (v : qvec) : qvec :=
  map (fun kc => (kc.1, Qred (Qmult a kc.2))) v.

End Vec.

Definition meq (a b : mono) : bool := a == b.

Definition mvec (p : mpoly) : qvec mono := map (fun t => (t.2, inject_Z t.1)) p.

(* an echelon row: pivot, vector (1 at the pivot), combination of the
   generators it stands for *)
Definition erow := (mono * qvec mono * qvec nat)%type.

Definition reduce (rows : seq erow) (vc : qvec mono * qvec nat) :=
  foldl (fun vc (r : erow) =>
           let a := vget meq r.1.1 vc.1 in
           if Qeq_bool a q0 then vc
           else (vaxpy meq (Qopp a) r.1.2 vc.1, vaxpy Nat.eqb (Qopp a) r.2 vc.2))
        vc rows.

(* Gaussian elimination, generators in order; returns, for every dependent
   generator g, the combination c with c_g = 1 and sum c_h gen_h = 0 *)
Fixpoint elim (rows : seq erow) (gens : seq (nat * qvec mono))
    (acc : seq (nat * qvec nat)) : seq (nat * qvec nat) :=
  match gens with
  | [::] => acc
  | (g, v) :: gs =>
    let vc := reduce rows (v, [:: (g, q1)]) in
    match vc.1 with
    | [::] => elim rows gs ((g, vc.2) :: acc)
    | (m, a) :: _ =>
      let ia := Qinv a in
      elim (rcons rows (m, vscale ia vc.1, vscale ia vc.2)) gs acc
    end
  end.

Fixpoint dedup (l : seq mpoly) : seq mpoly :=
  if l is p :: l' then
    if has (meqb p) l' then dedup l' else p :: dedup l'
  else [::].

Fixpoint remove1 (p : mpoly) (l : seq mpoly) : seq mpoly :=
  if l is q :: l' then if meqb p q then l' else q :: remove1 p l' else [::].

(* stable insertion sort on a nat key *)
Fixpoint insk (x : nat * nat) (l : seq (nat * nat)) : seq (nat * nat) :=
  if l is y :: l' then if (x.2 < y.2)%N then x :: l else y :: insk x l'
  else [:: x].
Definition sortk (l : seq (nat * nat)) := foldr insk [::] (rev l).

Definition plcm (a b : positive) : positive := Z.to_pos (Z.lcm (Zpos a) (Zpos b)).

Definition qnum_at (d : positive) (q : QQ) : BinNums.Z :=
  (* q * d, an integer when Qden q divides d *)
  Z.div (Z.mul (Qnum q) (Zpos d)) (Zpos (Qden q)).

(* the plan: for each argument j to rewrite (outermost first), the list of
   (k, letter) with  exp A_j = prod letter ^ k *)
Definition eplan (res : seq re) (hs : seq nat) (lns : seq nat) :
    seq (nat * seq (BinNums.Z * lref)) :=
  let rfs := map re2rf res in
  let k := size rfs in
  let nl := size lns in
  let ok := fun j => ~~ nilp (nth (mone, mone) rfs j).2 in
  let js := filter ok (iota 0 k) in
  let dens := dedup (map (fun j => (nth (mone, mone) rfs j).2) js) in
  let D := mprod dens in
  let gone := (0%N, mvec D) in
  let gln := map (fun i => (i.+1, mvec (mmul D (mvar (nth 0%N lns i)))))
                 (iota 0 nl) in
  let size_of j := let x := nth (mone, mone) rfs j in
                   (nth 0%N hs j * 1000 + size x.1 + size x.2)%N in
  let order := map fst (sortk (map (fun j => (j, size_of j)) js)) in
  let garg := map (fun j => let x := nth (mone, mone) rfs j in
                    ((nl.+1 + j)%N, mvec (mmul x.1 (mprod (remove1 x.2 dens)))))
                  order in
  let deps := elim [::] (gone :: gln ++ garg) [::] in
  (* relation of a dependent argument: A_j = - sum_{h <> g} c_h gen_h *)
  let deps := filter (fun gc => (nl < gc.1)%N) deps in
  let coef gc h := Qred (Qopp (vget Nat.eqb h gc.2)) in
  let d0 := foldl (fun d gc => plcm d (Qden (coef gc 0%N))) 1%positive deps in
  let db b := foldl (fun d gc => plcm d (Qden (coef gc (nl.+1 + b)%N)))
                    1%positive deps in
  let isdep j := has (fun gc => gc.1 == (nl.+1 + j)%N) deps in
  let rel gc :=
    let c := coef gc 0%N in
    let cst := if Qeq_bool c q0 then [::] else [:: (qnum_at d0 c, LOne d0)] in
    let lnp := flatten (map (fun i =>
                 let r := coef gc i.+1 in
                 if Qeq_bool r q0 then [::]
                 else [:: (Qnum r, LLn (nth 0%N lns i) (Qden r))]) (iota 0 nl)) in
    let argp := flatten (map (fun b =>
                 if b == (gc.1 - nl.+1)%N then [::] else
                 let s := coef gc (nl.+1 + b)%N in
                 if Qeq_bool s q0 then [::]
                 else [:: (qnum_at (db b) s, LExp b (db b))]) (iota 0 k)) in
    (gc.1 - nl.+1, cst ++ lnp ++ argp)%N in
  let basis := flatten (map (fun b =>
                 if isdep b || ~~ ok b then [::] else
                 let d := db b in
                 if d is xH then [::] else [:: (b, [:: (Zpos d, LExp b d)])])
               (iota 0 k)) in
  let alls := map rel deps ++ basis in
  (* outermost first: larger index of the post-order first *)
  let idx := map fst (sortk (map (fun x => (x.1, k - x.1)%N) alls)) in
  flatten (map (fun j => filter (fun x => x.1 == j) alls) idx).

End SearchExp.

(* ------------------------------------------------------------------------- *)
(* ln side: factorisation                                                    *)
(* ------------------------------------------------------------------------- *)

(* polynomial expressions over numbered atoms (output of the ln search) *)
Inductive pe : Type :=
  | PVar of nat | PCst of BinNums.Z | PAdd of pe & pe | PSub of pe & pe
  | PMul of pe & pe | POpp of pe | PPow of pe & nat.

Section SearchLn.
Local Open Scope Z_scope.
Import MFactor.

(* monomial x_0^e_0 ... as a product, None if constant *)
Fixpoint mono_pe (i : nat) (e : mono) : option pe :=
  match e with
  | [::] => None
  | k :: e' =>
    let m := match k with O => None | 1%N => Some (PVar i)
                        | _ => Some (PPow (PVar i) k) end in
    match m, mono_pe i.+1 e' with
    | None, r => r
    | Some a, None => Some a
    | Some a, Some b => Some (PMul a b)
    end
  end.

Definition term_pe (c : Z) (e : mono) : pe :=
  match mono_pe 0 e with
  | None => PCst c
  | Some m => if c =? 1 then m else PMul (PCst c) m
  end.

Definition poly_pe (p : mpoly) : pe :=
  match p with
  | [::] => PCst 0
  | (c, e) :: p' =>
    foldl (fun acc t => if 0 <? t.1 then PAdd acc (term_pe t.1 t.2)
                        else PSub acc (term_pe (- t.1) t.2))
          (if 0 <? c then term_pe c e else POpp (term_pe (- c) e)) p'
  end.

(* numerator and denominator, without simplification *)
Fixpoint re2f (e : re) : mpoly * mpoly :=
  match e with
  | RVar i => (mvar i, mone)
  | RCst c => (mconst c, mone)
  | RAdd a b =>
    let (na, da) := re2f a in let (nb, db) := re2f b in
    if meqb da db then (madd na nb, da)
    else (madd (mmul na db) (mmul nb da), mmul da db)
  | RSub a b =>
    let (na, da) := re2f a in let (nb, db) := re2f b in
    if meqb da db then (msub na nb, da)
    else (msub (mmul na db) (mmul nb da), mmul da db)
  | RMul a b =>
    let (na, da) := re2f a in let (nb, db) := re2f b in
    (mmul na nb, mmul da db)
  | RDiv a b =>
    let (na, da) := re2f a in let (nb, db) := re2f b in
    (mmul na db, mmul da nb)
  | ROpp a => let (na, da) := re2f a in (mopp na, da)
  | RPow a k => let (na, da) := re2f a in (mpow na k, mpow da k)
  | RInv a => let (na, da) := re2f a in (da, na)
  end.

(* irreducible non-constant factors, primitive, positive leading coeff. *)
Definition nfactors (p : mpoly) : seq (mpoly * nat) :=
  mgroup [seq mprim f | f <- MFactorEEZ.mfactor_full p & ~~ nilp (mvars f)].

(* the constant c with p = c * prod f ^ k *)
Definition ncontent (p : mpoly) (g : seq (mpoly * nat)) : Z :=
  Z.div (mlc p) (foldr (fun fk c => c * mlc fk.1 ^ Z.of_nat fk.2) 1 g).

Fixpoint zgroup (l : seq Z) : seq (Z * nat) :=
  if l is q :: l' then
    let g := zgroup l' in
    if has (fun qk => qk.1 =? q) g then
      map (fun qk => if qk.1 =? q then (qk.1, qk.2.+1) else qk) g
    else (q, 1%N) :: g
  else [::].

(* exponents of a numerator group minus those of a denominator group *)
Definition gcomb (A : Type) (eqA : A -> A -> bool)
    (gn gd : seq (A * nat)) : seq (A * Z) :=
  let mult g a := if has (fun bk => eqA bk.1 a) g then
                    (nth (a, 0%N) g (find (fun bk => eqA bk.1 a) g)).2
                  else 0%N in
  filter (fun az => ~~ (az.2 =? 0))
    ([seq (ak.1, Z.of_nat ak.2 - Z.of_nat (mult gd ak.1)) | ak <- gn] ++
     [seq (ak.1, - Z.of_nat ak.2) |
        ak <- gd & ~~ has (fun bk => eqA bk.1 ak.1) gn]).

(* Some (s, l): the argument is (+/-) prod (q ^ z) * prod (p ^ z), with
   + iff s; None if the numerator or the denominator is 0 *)
Definition lnfactor (e : re) : option (bool * seq (pe * Z)) :=
  let (n, d) := re2f e in
  if nilp n || nilp d then None else
  let gn := nfactors n in
  let gd := nfactors d in
  let cn := ncontent n gn in
  let cd := ncontent d gd in
  let s := (0 <? cn) == (0 <? cd) in
  let cs := @gcomb _ Z.eqb (zgroup (zprimes cn)) (zgroup (zprimes cd)) in
  let ps := @gcomb _ meqb gn gd in
  Some (s, [seq (PCst qz.1, qz.2) | qz <- cs] ++
           [seq (poly_pe pz.1, pz.2) | pz <- ps]).

End SearchLn.

(* ========================================================================= *)
(* The proved part                                                           *)
(* ========================================================================= *)

Unset Implicit Arguments.
Local Open Scope R_scope.

Fixpoint pnth (l : list R) (i : nat) : R :=
  match l, i with
  | nil, _ => 0
  | cons a _, O => a
  | cons _ l', S i' => pnth l' i'
  end.

(* ------------------------------------------------------------------------- *)
(* exp side                                                                  *)
(* ------------------------------------------------------------------------- *)

Definition lref_eval (atoms args : list R) (r : lref) : R :=
  match r with
  | LOne xH => 1
  | LOne d => 1 / IZR (Zpos d)
  | LLn i xH => pnth atoms i
  | LLn i q => pnth atoms i / IZR (Zpos q)
  | LExp b xH => pnth args b
  | LExp b d => pnth args b / IZR (Zpos d)
  end.

Fixpoint lmap (atoms args : list R) (l : list (BinNums.Z * lref)) :
    list (BinNums.Z * R) :=
  match l with
  | nil => nil
  | cons (k, r) l' => cons (k, lref_eval atoms args r) (lmap atoms args l')
  end.

Definition zpow (x : R) (k : BinNums.Z) : R :=
  match k with
  | Z0 => 1
  | Zpos xH => x
  | Zpos p => x ^ Pos.to_nat p
  | Zneg xH => / x
  | Zneg p => / x ^ Pos.to_nat p
  end.

Fixpoint lsum (l : list (BinNums.Z * R)) : R :=
  match l with
  | nil => 0
  | cons (k, a) l' => IZR k * a + lsum l'
  end.

Fixpoint lprod (l : list (BinNums.Z * R)) : R :=
  match l with
  | nil => 1
  | cons (k, a) nil => zpow (exp a) k
  | cons (k, a) l' => zpow (exp a) k * lprod l'
  end.

Lemma exp_mul_nat n a : exp (INR n * a) = exp a ^ n.
Proof.
elim: n => [|n IH]; first by rewrite /= Rmult_0_l exp_0.
rewrite S_INR Rmult_plus_distr_r Rmult_1_l exp_plus IH /=; lra.
Qed.

Lemma exp_mul_pos p a : exp (IZR (Zpos p) * a) = exp a ^ Pos.to_nat p.
Proof. by rewrite -exp_mul_nat INR_IPR. Qed.

Lemma exp_zpow k a : exp (IZR k * a) = zpow (exp a) k.
Proof.
case: k => [|p|p]; first by rewrite /= Rmult_0_l exp_0.
  rewrite exp_mul_pos; case: p => [p|p|] //=; lra.
rewrite IZR_NEG -Ropp_mult_distr_l exp_Ropp exp_mul_pos.
by case: p => [p|p|] //=; rewrite Rmult_1_r.
Qed.

Lemma exp_lsum l : exp (lsum l) = lprod l.
Proof.
elim: l => [|[k a] l IH] /=; first by rewrite exp_0.
rewrite exp_plus IH exp_zpow.
by case: l IH => [|? ?] //= _; rewrite Rmult_1_r.
Qed.

Lemma exp_lsumE a l : a = lsum l -> exp a = lprod l.
Proof. by move=> ->; exact: exp_lsum. Qed.

(* exp (ln a / q) is the real q-th root of a, a > 0 *)
Lemma exp_ln_div_root p a : 0 < a ->
  exp (ln a / IZR (Zpos p)) = rootR (Pos.to_nat p) a.
Proof.
move=> a0; have n0 : (0 < Pos.to_nat p)%N by apply/ltP; exact: Pos2Nat.is_pos.
rewrite -rootR_posrootE; symmetry; apply: proot_eq => //.
  by apply/RleP; apply: Rlt_le; exact: exp_pos.
rewrite -RpowE -exp_mul_nat INR_IPR.
have e : IZR (Zpos p) * (ln a / IZR (Zpos p)) = ln a.
  by field; apply: not_0_IZR.
by rewrite e exp_ln.
Qed.

Lemma sqrt_exp a : sqrt (exp a) = exp (a / 2).
Proof.
have e2 : exp a = exp (a / 2) ^ 2.
  by rewrite -(exp_mul_pos 2); congr exp; field.
rewrite e2 sqrt_pow2 //; exact: Rlt_le (exp_pos _).
Qed.

Lemma ln_gt_0' a : 1 < a -> 0 < ln a.
Proof. by move=> a1; rewrite -ln_1; apply: ln_increasing => //; lra. Qed.

(* ------------------------------------------------------------------------- *)
(* ln side                                                                   *)
(* ------------------------------------------------------------------------- *)

Fixpoint pe_eval (l : list R) (e : pe) : R :=
  match e with
  | PVar i => pnth l i
  | PCst c => IZR c
  | PAdd a b => pe_eval l a + pe_eval l b
  | PSub a b => pe_eval l a - pe_eval l b
  | PMul a b => pe_eval l a * pe_eval l b
  | POpp a => - pe_eval l a
  | PPow a n => pe_eval l a ^ n
  end.

(* the letter ln |x|, a marker used during the ln pass *)
Definition Lnabs (x : R) : R := ln (Rabs x).

Definition zpw (x : R) (z : BinNums.Z) : R :=
  match z with
  | Z0 => 1
  | Zpos p => x ^ Pos.to_nat p
  | Zneg p => / x ^ Pos.to_nat p
  end.

Fixpoint fprod (l : list R) (fs : seq (pe * BinNums.Z)) : R :=
  if fs is (p, z) :: fs' then zpw (pe_eval l p) z * fprod l fs' else 1.

Fixpoint fsum (l : list R) (fs : seq (pe * BinNums.Z)) : R :=
  if fs is (p, z) :: fs' then IZR z * Lnabs (pe_eval l p) + fsum l fs'
  else 0.

Fixpoint fnz (l : list R) (fs : seq (pe * BinNums.Z)) : Prop :=
  if fs is (p, _) :: fs' then pe_eval l p <> 0 /\ fnz l fs' else True.

Definition feval (s : bool) (l : list R) (fs : seq (pe * BinNums.Z)) : R :=
  if s then fprod l fs else - fprod l fs.

Lemma pow_neq0 x n : x <> 0 -> x ^ n <> 0.
Proof. by move=> x0; apply: pow_nonzero. Qed.

Lemma zpw_neq0 x z : x <> 0 -> zpw x z <> 0.
Proof.
move=> x0; case: z => [|p|p] /=; first exact: R1_neq_R0.
  exact: pow_neq0.
by apply: Rinv_neq_0_compat; apply: pow_neq0.
Qed.

Lemma lnabs_zpw x z : x <> 0 -> Lnabs (zpw x z) = IZR z * Lnabs x.
Proof.
move=> x0; have ax : 0 < Rabs x by exact: Rabs_pos_lt.
rewrite /Lnabs; case: z => [|p|p] /=.
- by rewrite Rabs_R1 ln_1 Rmult_0_l.
- by rewrite -RPow_abs ln_pow // INR_IPR.
- have h : 0 < Rabs x ^ Pos.to_nat p by exact: pow_lt.
  by rewrite Rabs_inv -RPow_abs ln_Rinv // ln_pow // INR_IPR Ropp_mult_distr_l.
Qed.

Lemma fprod_neq0 l fs : fnz l fs -> fprod l fs <> 0.
Proof.
elim: fs => [|[p z] fs IH] /=; first by move=> _; exact: R1_neq_R0.
move=> [p0 /IH f0]; apply: Rmult_integral_contrapositive_currified => //.
exact: zpw_neq0.
Qed.

Lemma lnabs_fprod l fs : fnz l fs -> Lnabs (fprod l fs) = fsum l fs.
Proof.
elim: fs => [|[p z] fs IH] /=; first by move=> _; rewrite /Lnabs Rabs_R1 ln_1.
move=> [p0 f0]; have z0 := zpw_neq0 _ z p0; have g0 := fprod_neq0 _ _ f0.
rewrite -(IH f0) -(lnabs_zpw _ z p0) /Lnabs Rabs_mult ln_mult //.
  exact: Rabs_pos_lt.
exact: Rabs_pos_lt.
Qed.

(* the split of ln |A| along a checked factorisation *)
Lemma lnabs_fact A s l fs :
  A = feval s l fs -> fnz l fs -> ln (Rabs A) = fsum l fs.
Proof.
move=> -> f0; rewrite -(lnabs_fprod _ _ f0) /feval /Lnabs.
by case: s => //; rewrite Rabs_Ropp.
Qed.

(* the same factorisation gives d <> 0 *)
Lemma feval_neq0 d s l fs : d = feval s l fs -> fnz l fs -> d <> 0.
Proof.
move=> -> /fprod_neq0 f0; case: s => //=.
exact: Ropp_neq_0_compat.
Qed.

(* and 0 < A when the sign is + and all exponents of polynomials are even *)
Definition fposb (fs : seq (pe * BinNums.Z)) : bool :=
  all (fun pz => if pz.1 is PCst q then Z.ltb 0 q else Z.even pz.2) fs.

Lemma zpw_pos x z : x <> 0 -> (0 < x \/ Z.even z) -> 0 < zpw x z.
Proof.
move=> x0 h; case: z h => [|p|p] /= h; first lra.
- case: h => [x1|]; first exact: pow_lt.
  case: p => // p _; rewrite Pos2Nat.inj_xO pow_mult; apply: pow_lt.
  by rewrite -Rsqr_pow2; exact: Rsqr_pos_lt.
- apply: Rinv_0_lt_compat; case: h => [x1|]; first exact: pow_lt.
  case: p => // p _; rewrite Pos2Nat.inj_xO pow_mult; apply: pow_lt.
  by rewrite -Rsqr_pow2; exact: Rsqr_pos_lt.
Qed.

Lemma fprod_pos l fs : fnz l fs -> fposb fs -> 0 < fprod l fs.
Proof.
elim: fs => [|[p z] fs IH] /=; first by move=> _ _; lra.
move=> [p0 f0] /andP[hp hf]; apply: Rmult_lt_0_compat; last exact: IH.
apply: zpw_pos => //; case: p p0 hp => /=; try by right.
by move=> q _ /Z.ltb_lt q0; left; apply: IZR_lt.
Qed.

Lemma pos_fact A l fs :
  A = feval true l fs -> fnz l fs -> fposb fs -> 0 < A.
Proof. by move=> -> f0 fp; apply: fprod_pos. Qed.

Lemma ln_abs_pos a : 0 < a -> ln a = ln (Rabs a).
Proof. by move=> a0; rewrite Rabs_pos_eq //; apply: Rlt_le. Qed.

Lemma Lnabs_exp b : Lnabs (exp b) = b.
Proof. by rewrite /Lnabs Rabs_pos_eq ?ln_exp //; apply: Rlt_le; apply: exp_pos. Qed.

Lemma Lnabs_abs b : Lnabs (Rabs b) = ln (Rabs b).
Proof. by rewrite /Lnabs Rabs_Rabsolu. Qed.

Lemma Lnabs_num p : Lnabs (IZR (Zpos p)) = ln (IZR (Zpos p)).
Proof. by rewrite /Lnabs Rabs_pos_eq //; apply: IZR_le. Qed.

(* ========================================================================= *)
(* Conditions                                                                *)
(* ========================================================================= *)

(* 0 < exp a for every exp a of the goal *)
Ltac exp_pos_hyps :=
  repeat match goal with
  | |- context [exp ?a] =>
    lazymatch goal with
    | _ : 0 < exp a |- _ => fail
    | _ => have := exp_pos a; move=> ?
    end
  end.

Ltac explog_pos :=
  solve [ first [ exact: exp_pos | assumption | lra
        | apply: Rabs_pos_lt; explog_nz
        | apply: Rplus_lt_0_compat; explog_pos
        | apply: Rplus_le_lt_0_compat; [apply: Rlt_le|]; explog_pos
        | apply: Rmult_lt_0_compat; explog_pos
        | apply: Rdiv_lt_0_compat; explog_pos
        | apply: pow_lt; explog_pos
        | apply: Rinv_0_lt_compat; explog_pos
        | apply: sqrt_lt_R0; explog_pos
        | apply: ln_gt_0'; lra
        | nra
        | exp_pos_hyps; nra ] ]
with explog_nz :=
  solve [ first [ assumption
        | apply: Rgt_not_eq; explog_pos
        | apply: Rlt_not_eq; solve [lra | nra]
        | apply: pow_neq0; explog_nz
        | apply: Rinv_neq_0_compat; explog_nz
        | apply: Rmult_integral_contrapositive_currified; explog_nz
        | apply: Ropp_neq_0_compat; explog_nz
        | exp_pos_hyps; apply: Rgt_not_eq; nra
        | exp_pos_hyps; apply: Rlt_not_eq; nra ] ].

Ltac explog_easy := first [ explog_pos | explog_nz ].

(* H2 (heuristic layer, defined here because the core calls it): a
   condition p <> 0 implied by the context (e.g. by 0 < p ^ 2 - 1) is
   dropped; nra by contradiction, it may miss implications *)
Ltac explog_implied :=
  lazymatch goal with
  | |- _ <> _ => let h := fresh "h" in solve [move=> h; nra]
  end.

(* H4 (heuristic layer, defined here because the core calls it): Rabs p is
   rewritten to p when 0 <= p is easy *)
Ltac abs_clean :=
  repeat match goal with
  | |- context [Rabs ?p] =>
    let hp := fresh "hp" in
    (have hp : 0 <= p by first [ apply: Rlt_le; explog_pos | lra ]);
    rewrite (Rabs_pos_eq p hp); clear hp
  end.

(* a condition is proved by the context or easily *)
Ltac use_cond0 := first [ assumption | explog_easy | explog_implied ].
Ltac use_cond :=
  try unfold Lnabs; first [ use_cond0 | progress abs_clean; use_cond0 ].

(* The conditions that are not closed are collected in a "bag": a
   hypothesis HB : Bag (c_1 /\ ... /\ c_n /\ ?tail) of the main goal whose
   proof is a single shelved goal; ?tail is instantiated by c /\ ?tail' when
   a condition c is added, by True at the end.  The bag goal is given back
   after the main goal and cleaned (H2: a condition implied by the others is
   dropped, bag_clean). *)
Definition Bag (P : Prop) : Prop := P.

Lemma bag_intro (C G : Prop) : Bag C -> (Bag C -> G) -> G.
Proof. by move=> c; apply. Qed.

Lemma bag_drop (a r : Prop) : (r -> a) -> r -> a /\ r.
Proof. by move=> ra r0; split => //; apply: ra. Qed.

Lemma bag_keep (a r : Prop) : a -> (a -> r) -> a /\ r.
Proof. by move=> a0 ar; split => //; apply: ar. Qed.

Ltac bag_tail E := lazymatch E with _ /\ ?r => bag_tail r | _ => E end.

Ltac bag_mem E c :=
  lazymatch E with
  | ?a /\ ?r => tryif constr_eq a c then idtac else bag_mem r c
  end.

Ltac bag_proof p E c :=
  lazymatch E with
  | ?a /\ ?r =>
    tryif constr_eq a c then exact (proj1 p)
    else bag_proof constr:(proj2 p) r c
  end.

(* hc : c in the context, c put in the bag if it is not there yet *)
Ltac bag_add c :=
  lazymatch goal with
  | HB : Bag ?E |- _ =>
    tryif bag_mem E c then idtac else
      (let T := bag_tail E in
       let t := open_constr:(c /\ _) in
       unify T t);
    lazymatch goal with
    | HB : Bag ?E |- _ =>
      let h := fresh "hc" in assert (h : c) by bag_proof HB E c
    end
  end.

Ltac bag_close :=
  lazymatch goal with
  | HB : Bag ?E |- _ => let T := bag_tail E in unify T True
  end.

Ltac bag_clear := lazymatch goal with HB : Bag _ |- _ => clear HB end.

(* a condition c: nothing if already in the context or easy (H2), otherwise
   put in the bag and kept as a hypothesis hc : c *)
Ltac add_cond c0 :=
  let c := eval cbv [Lnabs] in c0 in
  lazymatch goal with
  | _ : c |- _ => idtac
  | _ => first [ assert_succeeds (assert c by use_cond) | bag_add c ]
  end.

Ltac add_conds C :=
  lazymatch C with
  | ?a /\ ?b => add_cond a; add_conds b
  | True => idtac
  | ?a => add_cond a
  end.

(* the conditions of field: closed from the context, otherwise bagged *)
Ltac field_conds :=
  repeat split;
  first [ solve [use_cond]
        | lazymatch goal with |- ?c => add_cond c; assumption end ].

(* ========================================================================= *)
(* Reification (shared)                                                      *)
(* ========================================================================= *)

Ltac natcst n := lazymatch n with O => constr:(true) | S ?m => natcst m end.

Ltac poscst p :=
  lazymatch p with
  | xH => constr:(true) | xO ?q => poscst q | xI ?q => poscst q
  end.

Ltac zcst z :=
  lazymatch z with
  | Z0 => constr:(true) | Zpos ?p => poscst p | Zneg ?p => poscst p
  end.

Ltac ceq a b := match a with b => constr:(true) | _ => constr:(false) end.

Ltac inlist t l :=
  lazymatch l with
  | nil => constr:(false)
  | cons ?h ?r =>
    let b := ceq t h in
    lazymatch b with true => constr:(true) | false => inlist t r end
  end.

Ltac snoc t l :=
  lazymatch l with
  | nil => constr:(@cons R t (@nil R))
  | cons ?h ?r => let r' := snoc t r in constr:(@cons R h r')
  end.

Ltac snocN t l :=
  lazymatch l with
  | nil => constr:(@cons nat t (@nil nat))
  | cons ?h ?r => let r' := snocN t r in constr:(@cons nat h r')
  end.

Ltac ladd t l := let b := inlist t l in
  lazymatch b with true => l | false => snoc t l end.

Ltac idx t l :=
  lazymatch l with
  | cons ?h ?r =>
    let b := ceq t h in
    lazymatch b with
    | true => constr:(O)
    | false => let n := idx t r in constr:(S n)
    end
  end.

Ltac lnth l n :=
  lazymatch n with
  | O => lazymatch l with cons ?h _ => h end
  | S ?m => lazymatch l with cons _ ?r => lnth r m end
  end.

(* atoms of a rational expression, appended to l (indices of l are kept) *)
Ltac rcollect t l :=
  match t with
  | ?a + ?b => let l := rcollect a l in rcollect b l
  | ?a - ?b => let l := rcollect a l in rcollect b l
  | ?a * ?b => let l := rcollect a l in rcollect b l
  | ?a / ?b => let l := rcollect a l in rcollect b l
  | - ?a => rcollect a l
  | / ?a => rcollect a l
  | ?a ^ ?n => let _ := natcst n in rcollect a l
  | IZR ?z => let _ := zcst z in l
  | R0 => l
  | R1 => l
  | _ => ladd t l
  end.

Ltac rcollect_list A l :=
  lazymatch A with
  | nil => l
  | cons ?a ?r => let l := rcollect a l in rcollect_list r l
  end.

Ltac rreify l t :=
  match t with
  | ?a + ?b => let x := rreify l a in let y := rreify l b in constr:(RAdd x y)
  | ?a - ?b => let x := rreify l a in let y := rreify l b in constr:(RSub x y)
  | ?a * ?b => let x := rreify l a in let y := rreify l b in constr:(RMul x y)
  | ?a / ?b => let x := rreify l a in let y := rreify l b in constr:(RDiv x y)
  | - ?a => let x := rreify l a in constr:(ROpp x)
  | / ?a => let x := rreify l a in constr:(RInv x)
  | ?a ^ ?n => let _ := natcst n in
               let x := rreify l a in constr:(RPow x n)
  | IZR ?z => let _ := zcst z in constr:(RCst z)
  | R0 => constr:(RCst Z0)
  | R1 => constr:(RCst (Zpos xH))
  | _ => let i := idx t l in constr:(RVar i)
  end.

Ltac rreify_list l A :=
  lazymatch A with
  | nil => constr:(@nil re)
  | cons ?a ?r => let x := rreify l a in let y := rreify_list l r in
                  constr:(@cons re x y)
  end.

(* ========================================================================= *)
(* Core, ln pass (Theorem 5.7(a))                                            *)
(* ========================================================================= *)

Ltac fnz_hyps := cbv [fnz pe_eval pnth]; repeat split; use_cond.

Ltac mkT s l fs :=
  eval cbv [feval fprod zpw pe_eval pnth Pos.to_nat Pos.iter_op Nat.add]
    in (feval s l fs).

Ltac mkC l fs := eval cbv [fnz pe_eval pnth] in (fnz l fs).

(* hypothesis d <> 0, from the irreducible factors of d *)
Ltac nz_den l d :=
  lazymatch goal with
  | _ : d <> 0 |- _ => idtac
  | _ =>
    let e := rreify l d in
    let r := eval vm_compute in (lnfactor e) in
    lazymatch r with
    | Some (?s, ?fs) =>
      let T := mkT s l fs in
      let C := mkC l fs in
      add_conds C;
      lazymatch goal with
      | _ : d <> 0 |- _ => idtac
      | _ =>
        first [ assert_succeeds (assert (d <> 0) by use_cond)
              | let h := fresh "hd" in
                assert (h : d <> 0);
                  [ apply: (feval_neq0 d s l fs);
                    [ change (d = T); field; field_conds | fnz_hyps ] | ] ]
      end
    | None => add_cond (d <> 0)
    end
  end.

(* the denominators of t, innermost first *)
Ltac den_conds l t :=
  lazymatch t with
  | ?a + ?b => den_conds l a; den_conds l b
  | ?a - ?b => den_conds l a; den_conds l b
  | ?a * ?b => den_conds l a; den_conds l b
  | ?a / ?b => den_conds l a; den_conds l b; nz_den l b
  | / ?a => den_conds l a; nz_den l a
  | - ?a => den_conds l a
  | ?a ^ _ => den_conds l a
  | _ => idtac
  end.

(* the innermost ln of the goal *)
Ltac find_ln :=
  match goal with
  | |- context [ln ?a] =>
    lazymatch a with context [ln _] => fail | _ => constr:(Some a) end
  | _ => constr:(@None R)
  end.

(* ln |b| = sum, factorisation (s, fs) of b over the atoms l; when b is
   already a letter (one irreducible factor, itself) it is only marked *)
Ltac ln_split l b s fs :=
  let S := eval cbv [fsum pe_eval pnth] in (fsum l fs) in
  let lt := lazymatch S with
            | IZR (Zpos xH) * Lnabs ?p + 0 =>
                lazymatch s with true => ceq p b | false => constr:(false) end
            | _ => constr:(false)
            end in
  lazymatch lt with
  | true => change (ln (Rabs b)) with (Lnabs b); rewrite ?Lnabs_exp ?Lnabs_abs
  | false =>
    let T := mkT s l fs in
    let hS := fresh "hS" in
    have hS : ln (Rabs b) = S;
      [ apply: (lnabs_fact b s l fs);
        [ change (b = T); field; field_conds | fnz_hyps ] | ];
    rewrite ?Rmult_1_l ?Rplus_0_r in hS;
    rewrite hS ?Lnabs_exp ?Lnabs_abs; clear hS
  end.

(* one ln: ln (Rabs b) needs no condition, ln a needs 0 < a *)
Ltac ln_one l a :=
  lazymatch a with
  | Rabs ?b =>
    den_conds l b;
    let e := rreify l b in
    let r := eval vm_compute in (lnfactor e) in
    lazymatch r with
    | Some (?s, ?fs) => let C := mkC l fs in add_conds C; ln_split l b s fs
    | None => change (ln (Rabs b)) with (Lnabs b)
    end
  | _ =>
    den_conds l a;
    let e := rreify l a in
    let r := eval vm_compute in (lnfactor e) in
    lazymatch r with
    | Some (?s, ?fs) =>
      let C := mkC l fs in
      let T := mkT s l fs in
      let pb := eval vm_compute in (s && fposb fs) in
      lazymatch pb with
      | true =>
        (* 0 < a follows from the conditions p_i <> 0 *)
        add_conds C;
        lazymatch goal with
        | _ : 0 < a |- _ => idtac
        | _ =>
          first [ assert_succeeds (assert (0 < a) by use_cond)
                | let h := fresh "hc" in
                  assert (h : 0 < a) by
                    (apply: (pos_fact a l fs);
                       [ change (a = T); field; field_conds
                       | fnz_hyps | vm_compute; reflexivity ])
                | add_cond (0 < a) ]
        end
      | false =>
        (* 0 < a first: the conditions p_i <> 0 often follow from it *)
        add_cond (0 < a); add_conds C
      end;
      rewrite (ln_abs_pos a); last use_cond;
      ln_split l a s fs
    | None =>
      add_cond (0 < a);
      rewrite (ln_abs_pos a); last use_cond;
      change (ln (Rabs a)) with (Lnabs a)
    end
  end.

Ltac ln_loop l :=
  let o := find_ln in
  lazymatch o with
  | Some ?a =>
    let b := lazymatch a with Rabs ?b => b | _ => a end in
    let l := rcollect b l in ln_one l a; ln_loop l
  | None => idtac
  end.

Ltac explog_unletter := rewrite ?Lnabs_num; try unfold Lnabs.

(* the ln pass; conditions go to the bag *)
Ltac explog_ln := ln_loop (@nil R); explog_unletter.

(* ========================================================================= *)
(* Core, exp pass (Theorem 5.7(b))                                           *)
(* ========================================================================= *)

(* arguments of the exp terms, inner ones first (post-order) *)
Ltac ecollect t l :=
  lazymatch t with
  | exp ?a => let l := ecollect a l in ladd a l
  | ?f ?a => let l := ecollect f l in ecollect a l
  | _ => l
  end.

(* exp nesting depth *)
Ltac hgt t :=
  lazymatch t with
  | exp ?a => let h := hgt a in constr:(S h)
  | ?f ?a => let h1 := hgt f in let h2 := hgt a in
             let h := eval vm_compute in (Nat.max h1 h2) in h
  | _ => constr:(O)
  end.

Ltac maxh L :=
  lazymatch L with
  | nil => constr:(O)
  | cons ?a ?r => let h := hgt a in let m := maxh r in
                  let h := eval vm_compute in (Nat.max h m) in h
  end.

(* the arguments of height <= k, with their heights *)
Ltac hfilter L k A hs :=
  lazymatch L with
  | nil => constr:((A, hs))
  | cons ?a ?r =>
    let h := hgt a in
    let b := eval vm_compute in (Nat.leb h k) in
    lazymatch b with
    | true => let A := snoc a A in let hs := snocN h hs in hfilter r k A hs
    | false => hfilter r k A hs
    end
  end.

(* indices of the ln atoms *)
Ltac lnidx l i :=
  lazymatch l with
  | nil => constr:(@nil nat)
  | cons (ln _) ?r => let r' := lnidx r (S i) in constr:(@cons nat i r')
  | cons _ ?r => lnidx r (S i)
  end.

(* exp a = prod of letters, a = lsum Rl checked by field; the denominators
   of a and of the sum are conditions; nothing is done if the check fails *)
Ltac rewrite_one ats a Rl :=
  let S := eval cbv [lsum] in (lsum Rl) in
  let T := eval cbv [lprod zpow Pos.to_nat Pos.iter_op Nat.add] in (lprod Rl) in
  tryif constr_eq (exp a) T then idtac else
  let h := fresh "h" in
  first [ den_conds ats a; den_conds ats S;
          have h : exp a = T;
            [ change (exp a = lprod Rl); apply: exp_lsumE; change (a = S);
              field; field_conds
            | try rewrite h; clear h ]
        | idtac ].

Ltac apply_plan ats A pl :=
  lazymatch pl with
  | nil => idtac
  | cons (?j, ?lst) ?r =>
    let a := lnth A j in
    let Rl := eval cbv [lmap lref_eval pnth] in (lmap ats A lst) in
    rewrite_one ats a Rl; apply_plan ats A r
  end.

(* exp (ln a) = a, exp (ln a / q) = rootR q a, under 0 < a *)
Ltac exp_ln_clean :=
  repeat match goal with
  | |- context [exp (ln ?a / IZR (Zpos ?p))] =>
    let n := eval vm_compute in (Pos.to_nat p) in
    add_cond (0 < a);
    rewrite (@exp_ln_div_root p a : _ -> exp _ = rootR n a); last use_cond
  | |- context [exp (ln ?a)] =>
    add_cond (0 < a); rewrite (exp_ln a); last use_cond
  end.

Ltac explog_level k :=
  lazymatch goal with
  | |- ?g =>
    let L := ecollect g (@nil R) in
    let Ah := hfilter L k (@nil R) (@nil nat) in
    lazymatch Ah with
    | (nil, _) => idtac
    | (?A, ?hs) =>
      let ats := rcollect_list A (@nil R) in
      let res := rreify_list ats A in
      let lns := lnidx ats O in
      let pl := eval vm_compute in (eplan res hs lns) in
      apply_plan ats A pl; exp_ln_clean
    end
  end.

Ltac explog_levels k n :=
  lazymatch n with
  | O => idtac
  | S ?m => explog_level k; explog_levels (S k) m
  end.

(* the exp pass; conditions go to the bag *)
Ltac explog_exp :=
  rewrite ?sqrt_exp;
  lazymatch goal with
  | |- ?g =>
    let L := ecollect g (@nil R) in
    let H := maxh L in
    explog_levels O (S H)
  end.

(* ========================================================================= *)
(* Core: the loop, the zero test                                             *)
(* ========================================================================= *)

(* H5 (heuristic layer, defined here because the core loop calls it) --
   square roots inside ln arguments.
   The core treats sqrt a inside an ln argument as an atom (the "algebraic
   case" that TR223 leaves out), so ln |sqrt a| is a letter unrelated to
   ln |a|.  H5 rewrites ln |sqrt a| = ln |a| / 2; its condition sqrt a <> 0
   is the one the ln pass already asked for the factor sqrt a (so it is a
   hypothesis hc), and it implies 0 < a.  Heuristic: only square roots, and
   only once they are ln letters. *)
Lemma ln_abs_sqrt a : sqrt a <> 0 -> ln (Rabs (sqrt a)) = ln (Rabs a) / 2.
Proof.
move=> h.
have a0 : 0 < a.
  case: (Rle_or_lt a 0) => [ale|//].
  by case: h; apply: sqrt_neg_0.
have s0 : 0 < sqrt a by apply: sqrt_lt_R0.
have ea : a = sqrt a * sqrt a by rewrite sqrt_sqrt //; apply: Rlt_le.
rewrite (Rabs_pos_eq (sqrt a)); last by apply: Rlt_le.
rewrite (Rabs_pos_eq a); last by apply: Rlt_le.
have hl : ln a = ln (sqrt a) + ln (sqrt a).
  by rewrite {1}ea ln_mult.
rewrite hl; field.
Qed.

Ltac explog_h5 :=
  repeat match goal with
  | |- context [ln (Rabs (sqrt ?a))] =>
      rewrite (ln_abs_sqrt a); last first; [ first [ assumption | use_cond ] | ]
  end.

Ltac explog_unfold :=
  try unfold tanh; try unfold cosh, sinh; try unfold Rpower; try unfold Rlog;
  try unfold tan.

(* exp pass then ln pass, until the goal does not change (at most n) *)
Ltac explog_loop n :=
  lazymatch n with
  | O => idtac
  | S ?m =>
    lazymatch goal with
    | |- ?g =>
      explog_exp; explog_ln; try explog_h5;
      lazymatch goal with
      | |- ?g' => tryif constr_eq g g' then idtac else explog_loop m
      end
    end
  end.

Ltac explog_core := explog_loop constr:(5%nat).

Ltac explog_zero_core :=
  lazymatch goal with
  | |- @eq R ?l ?r =>
    lazymatch constr:((l, r)) with
    | context [cos _] => first [ radcan_trig | radcan_lra ]
    | context [sin _] => first [ radcan_trig | radcan_lra ]
    | context [tan _] => first [ radcan_trig | radcan_lra ]
    | _ => radcan_lra
    end
  end.

(* conditions left by the zero test (radcan's, in mathcomp notation) *)
(* a condition a <> b stated on a mathcomp sort, restated on R *)
Ltac neq_R :=
  try lazymatch goal with |- ~ (@eq _ ?a ?b) => change (not (@eq R a b)) end.

Ltac explog_close1 :=
  lazymatch goal with
  | |- _ /\ _ => split; explog_close1
  | |- ~ _ => neq_R; try solve [use_cond]
  | |- Rlt _ _ => try solve [use_cond]
  | |- is_true _ =>
    radcan_Rstd_back; neq_R;
    try solve [use_cond | apply: Rlt_le; explog_pos]
  | _ => idtac
  end.

Ltac explog_close := try explog_close1.

(* ========================================================================= *)
(* Heuristic layer                                                           *)
(* Not part of Theorem 5.7.  Each heuristic only performs rewrites proved in *)
(* Rocq (or fails), so it is sound; it may fail to help.                    *)
(* ========================================================================= *)

(* H1 -- zero test retried after field_simplify_eq.
   What: when radcan (radcan_lra / radcan_trig) fails on the normal form,
   the denominators are cleared by field_simplify_eq and the zero test is
   run again on the polynomial equation.
   Why a heuristic: it only works around a gap of radcan on some rational
   identities (e.g. tanh (x + y) after the exp pass); its conditions
   (denominators <> 0) are closed when easy (positivity of exp letters). *)
Ltac explog_h1 :=
  first [ explog_zero_core
        | field_simplify_eq; [explog_zero_core | ..] ].

(* H2 -- condition clean-up (explog_implied and add_cond above).
   What: a condition already in the context or in the bag is never asked
   again; a condition implied by a hypothesis or by an earlier condition is
   not asked:
   x <> 0 from 0 < x, 0 < Rabs p from p <> 0 (explog_pos), p <> 0 by nra
   from the context (explog_implied); the ln pass asks 0 < A before the
   conditions p_i <> 0 on the factors of A, so that these follow from it.
   At the end the bag c_1 /\ ... /\ c_n is cleaned: c_i is dropped when it
   follows from c_(i+1) ... c_n (bag_drop), otherwise it is kept and
   assumed for the next ones (bag_keep); a kept condition is made more
   readable by H4.
   Why a heuristic: implication is only tried with lra / nra / the
   positivity rules of explog_pos. *)
(* H3 -- trigonometric arguments of exp / ln.
   What: when an argument of exp or ln contains cos or sin, the double
   angle, sum and opposite formulas are expanded and sin t ^ 2 is replaced by
   1 - cos t ^ 2 (Stdlib lemmas, rewritten everywhere in the goal), so that
   the Pythagorean relation is visible to the factorisation of the ln pass
   and to the linear algebra of the exp pass.
   Why a heuristic: sin and cos are atoms for Theorem 5.7; this normal form
   covers only those formulas (no n * t for n > 2, no tan). *)
Lemma sin2_pow x : sin x ^ 2 = 1 - cos x ^ 2.
Proof. by move: (sin2_cos2 x); rewrite /Rsqr /=; lra. Qed.

Ltac has_trig_arg :=
  match goal with
  | |- context [exp ?a] =>
    lazymatch a with context [cos _] => idtac | context [sin _] => idtac end
  | |- context [ln ?a] =>
    lazymatch a with context [cos _] => idtac | context [sin _] => idtac end
  end.

Ltac explog_h3 :=
  tryif has_trig_arg then
    rewrite ?cos_neg ?sin_neg ?cos_plus ?sin_plus ?cos_minus ?sin_minus
            ?cos_2a_cos ?sin_2a ?sin2_pow
  else idtac.

(* H4 -- Rabs p back to p when 0 <= p is closed easily.
   What: ln (Rabs p) becomes ln p (and any Rabs p becomes p) when 0 < p is
   a hypothesis / condition or is proved by explog_pos (Rabs_pos_eq).
   It is also tried by use_cond (a hypothesis ln x <> 0 then proves the
   condition ln (Rabs x) <> 0 when 0 < x) and on the conditions given back.
   Why a heuristic: it is a readability step (letters shown as ln p) that
   also lets radcan see p instead of an opaque Rabs p. *)
Ltac explog_h4 := abs_clean.

(* H5 -- square roots inside ln arguments: see explog_h5 above the core loop. *)



(* H2, clean-up of the bag (see above) *)
Ltac bag_hyps h :=
  lazymatch type of h with
  | _ /\ _ => let h1 := fresh "hc" in let h2 := fresh "hc" in
               case: h => h1 h2; bag_hyps h2
  | _ => idtac
  end.

Ltac bag_clean :=
  lazymatch goal with
  | |- True => exact I
  | |- ?a /\ ?r =>
    first [ apply: (bag_drop a r);
              [ let h := fresh "hc" in move=> h; bag_hyps h; solve [use_cond]
              | bag_clean ]
          | apply: (bag_keep a r);
              [ try explog_h4
              | let h := fresh "hc" in move=> h; bag_clean ] ]
  end.

(* ========================================================================= *)
(* The tactic                                                                *)
(* ========================================================================= *)

(* the procedure up to the zero test zt; the bag goal is shelved *)
Ltac explog_run zt :=
  explog_unfold; explog_h3;
  eapply bag_intro; [ shelve | move=> HB ];
  explog_core; bag_close; bag_clear; explog_h4; zt.

(* the bag goal, given back last *)
Ltac explog_bag :=
  lazymatch goal with
  | |- Bag _ => rewrite /Bag; bag_clean
  | _ => idtac
  end.

(* the normal form: main goal first, then the conditions *)
Ltac explog_norm :=
  unshelve (explog_run idtac); cycle 1; explog_bag.

Ltac explog :=
  unshelve (explog_run explog_h1); cycle 1; explog_close; explog_bag.
