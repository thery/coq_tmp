(******************************************************************************)
(* RefCheck: facts and the proved checker of the refinement.                  *)
(*   fact       == (KGe, P) 0 <= P, (KGt, P) 0 < P, (KNe, P) P != 0           *)
(*   rimp1 r f  == the fact r implies f (P = a * R + b with the right signs)  *)
(*   ptriv f    == f holds on a constant                                      *)
(*   rfacts r   == the facts of the refined condition r (two for RInt)       *)
(*   comb_check fs s P ls c0 == P = sum ls_i * fs_i + c0, ls_i, c0 >= 0       *)
(*                 (csum, cpos, cstrict), with 0 < P if s                     *)
(*   nzf e      == polynomials whose nonzeroness gives e != 0                 *)
(*   bound_interp F b == the value of the bound b in F                        *)
(*   kI k v, fsI rt env fs == the meaning of facts                            *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan RefPoly.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Q_scope.

(* Facts and the checker *)

(* KGe: 0 <= P, KGt: 0 < P, KNe: P != 0 *)
Inductive fkind := KGe | KGt | KNe.

Definition fact := (fkind * poly)%type.

(* the fact r implies the fact f *)
Definition rimp1 (r f : fact) : bool :=
  let: (kr, R) := r in let: (kp, P) := f in
  if lrel P R is Some (a, b) then
    match kp, kr with
    | KGe, KNe | KGt, KNe => false
    | KGe, _ => Qle_bool 0 a && Qle_bool 0 b
    | KGt, KGt => qlt 0 a && Qle_bool 0 b
    | KGt, KGe => qlt 0 a && qlt 0 b
    | KNe, KNe => qz b && ~~ qz a
    | KNe, KGt => (qlt 0 a && Qle_bool 0 b) || (qlt a 0 && Qle_bool b 0)
    | KNe, KGe => (qlt 0 a && qlt 0 b) || (qlt a 0 && qlt b 0)
    end
  else false.

(* facts true on constants *)
Definition ptriv (f : fact) : bool :=
  let: (k, P) := f in
  if pnc P is [::] then
    let c := pconst_of P in
    match k with KGe => Qle_bool 0 c | KGt => qlt 0 c | KNe => ~~ qz c end
  else false.

Definition b2q (b : bound) : Q :=
  let: (neg, n, d) := b in
  if d is 0%N then 0
  else Qmake (if neg then Z.opp (Z.of_nat n) else Z.of_nat n) (Pos.of_nat d).

Definition q2b (q : Q) : bound :=
  let q := Qred q in
  (Z.ltb (Qnum q) 0, Z.abs_nat (Qnum q), Pos.to_nat (Qden q)).

Definition pvar (i : nat) : poly := patom (RVar i).

Definition mpoly (m : amono) : poly :=
  foldr (fun ak acc => pmul (ppow (patom ak.1) ak.2) acc) (pconst 1) m.

Definition pterm (t : bound * amono) : poly :=
  pmul (pconst (b2q t.1)) (mpoly t.2).

Definition spoly (s : side) : poly :=
  foldr (fun t acc => padd (pterm t) acc) [::] s.

Definition low_fact (s : bool) (b : bound) (i : nat) : fact :=
  (if s then KGt else KGe, padd (pvar i) (pconst (- b2q b))).

Definition upp_fact (s : bool) (b : bound) (i : nat) : fact :=
  (if s then KGt else KGe, padd (pconst (b2q b)) (pscale (-1) (pvar i))).

(* the facts of a refined condition *)
Definition rfacts (r : rcond) : seq fact :=
  match r with
  | RRaw (CGe0 e) => [:: (KGe, pnorm e)]
  | RRaw (CNeq0 e) => [:: (KNe, pnorm e)]
  | RLow s b i => [:: low_fact s b i]
  | RUpp s b i => [:: upp_fact s b i]
  | RInt s1 b1 i s2 b2 => [:: low_fact s1 b1 i; upp_fact s2 b2 i]
  | RNeq i b => [:: (KNe, padd (pvar i) (pconst (- b2q b)))]
  | RCmp s l r =>
    [:: (if s then KGt else KGe, padd (spoly r) (pscale (-1) (spoly l)))]
  | RDiff l r => [:: (KNe, padd (spoly l) (pscale (-1) (spoly r)))]
  end.

Definition is_ge (f : fact) : bool := if f.1 is KNe then false else true.

(* Combinations: P = sum l_i * R_i + c0 with l_i, c0 >= 0 *)

Fixpoint csum (fs : seq fact) (ls : seq Q) : poly :=
  match fs, ls with
  | f :: fs', l :: ls' => padd (pscale l f.2) (csum fs' ls')
  | _, _ => [::]
  end.

(* nonnegative multipliers, zero on the facts P != 0 *)
Fixpoint cpos (fs : seq fact) (ls : seq Q) : bool :=
  match fs, ls with
  | f :: fs', l :: ls' => Qle_bool 0 l && (qz l || is_ge f) && cpos fs' ls'
  | _, _ => true
  end.

(* a positive multiplier on a fact 0 < R *)
Fixpoint cstrict (fs : seq fact) (ls : seq Q) : bool :=
  match fs, ls with
  | f :: fs', l :: ls' =>
    (if f.1 is KGt then qlt 0 l else false) || cstrict fs' ls'
  | _, _ => false
  end.

(* the certificate (ls, c0) shows 0 <= P (0 < P if strict) from fs *)
Definition comb_check (fs : seq fact) (strict : bool) (P : poly)
    (ls : seq Q) (c0 : Q) : bool :=
  [&& cpos fs ls, Qle_bool 0 c0, peqb P (padd (csum fs ls) (pconst c0))
    & ~~ strict || qlt 0 c0 || cstrict fs ls].

(* a monomial c * a1^k1 * ... is nonzero when c and the ai are *)
Definition msplit (p : poly) : seq poly :=
  if p is [:: (c, m)] then pconst c :: map (fun ak => patom ak.1) m else [:: p].

(* e is nonzero when all the nzf e are *)
Fixpoint nzf (e : rexpr) : seq poly :=
  match e with
  | RMul a b => nzf a ++ nzf b
  | RPow a _ | ROpp a | RInv a => nzf a
  | _ => msplit (pnorm e)
  end.

Local Close Scope Q_scope.
Local Open Scope ring_scope.

(* the value of a bound *)

Definition nat2F (F : numFieldType) (n : nat) : F :=
  match n with 0%N => 0 | 1%N => 1 | _ => n%:R end.

Definition bound_interp (F : numFieldType) (b : bound) : F :=
  let: (neg, n, d) := b in
  let v := if Nat.eqb d 1 then nat2F F n else nat2F F n / nat2F F d in
  if neg then - v else v.

Section CheckProofs.
Variable F : numFieldType.

Local Arguments Qred : simpl never.
Local Arguments Qplus : simpl never.
Local Arguments Qmult : simpl never.
Local Arguments Qopp : simpl never.
Local Arguments Qinv : simpl never.

Lemma nat2FE n : nat2F F n = n%:R.
Proof. by case: n => [|[]]. Qed.

Lemma bound_interpE b : bound_interp F b = Q2F (b2q b).
Proof.
case: b => [[neg n] [|d]].
  rewrite /bound_interp /= !nat2FE invr0 mulr0.
  by case: neg; rewrite /Q2F /= ?oppr0 mul0r.
rewrite /bound_interp /b2q /Q2F /= !nat2FE.
have -> : pos2F F (Pos.of_nat d.+1) = d.+1%:R by rewrite /pos2F Nat2Pos.id.
case: d => [|d].
  by case: neg => /=; rewrite ?Z2F_opp Z2F_nat divr1.
by case: neg => /=; rewrite ?Z2F_opp Z2F_nat ?mulNr.
Qed.

Variables (rt : nat -> F -> F) (env : seq F).
Local Notation ri := (rinterp_gen rt env).
Local Notation aeval := (aeval rt env).
Local Notation peval := (peval rt env).
Local Notation qzP := (@qzP F).
Local Notation Q2F_neq0 := (@Q2F_neq0 F).
Local Notation Q2F_gt0b := (@Q2F_gt0b F).
Local Notation Q2F_lt0b := (@Q2F_lt0b F).
Local Notation Q2F_ge0b := (@Q2F_ge0b F).
Local Notation Q2F_le0b := (@Q2F_le0b F).
Local Notation peqb_sound := (@peqb_sound F rt env).
Local Notation pconst_ofE := (@pconst_ofE F rt env).
Local Notation lrel_sound := (@lrel_sound F rt env).

Definition kI (k : fkind) (v : F) : Prop :=
  match k with KGe => 0 <= v | KGt => 0 < v | KNe => v != 0 end.

Lemma comb_gt0 (A B q : F) : 0 < A -> 0 <= B -> 0 < q -> 0 < A * q + B.
Proof. by move=> A0 B0 q0; rewrite ltr_wpDr // mulr_gt0. Qed.

Lemma comb_gt0' (A B q : F) : 0 < A -> 0 < B -> 0 <= q -> 0 < A * q + B.
Proof. by move=> A0 B0 q0; rewrite ltr_pwDr // mulr_ge0 // ltW. Qed.

Lemma comb_neg (A B q : F) : 0 < - A * q + - B -> A * q + B != 0.
Proof. by rewrite mulNr -opprD oppr_gt0 => /ltr0_neq0. Qed.

Lemma rimp1_sound r f : rimp1 r f -> kI r.1 (peval r.2) -> kI f.1 (peval f.2).
Proof.
case: r f => kr R [kp P] /=.
case E : (lrel P R) => [[a b]|] //; rewrite (lrel_sound E).
case: kp; case: kr => //=.
- by case/andP => /Q2F_ge0b A /Q2F_ge0b B q; rewrite addr_ge0 // mulr_ge0.
- case/andP => /Q2F_ge0b A /Q2F_ge0b B q.
  by rewrite addr_ge0 // mulr_ge0 // ltW.
- by case/andP => /Q2F_gt0b A /Q2F_gt0b B q; rewrite comb_gt0'.
- by case/andP => /Q2F_gt0b A /Q2F_ge0b B q; rewrite comb_gt0.
- case/orP => /andP [].
    by move=> /Q2F_gt0b A /Q2F_gt0b B q; rewrite lt0r_neq0 // comb_gt0'.
  move=> /Q2F_lt0b A /Q2F_lt0b B q; apply: comb_neg.
  by rewrite comb_gt0' ?oppr_gt0.
- case/orP => /andP [].
    by move=> /Q2F_gt0b A /Q2F_ge0b B q; rewrite lt0r_neq0 // comb_gt0.
  move=> /Q2F_lt0b A /Q2F_le0b B q; apply: comb_neg.
  by rewrite comb_gt0 ?oppr_gt0 ?oppr_ge0.
by case/andP => /qzP -> /Q2F_neq0 A q; rewrite addr0 mulf_neq0.
Qed.

Lemma ptriv_sound f : ptriv f -> kI f.1 (peval f.2).
Proof.
case: f => k P /=; rewrite (pconst_ofE P) /ptriv.
case: (pnc P) => //=; rewrite addr0.
by case: k => /=; [exact: Q2F_ge0b|exact: Q2F_gt0b|exact: Q2F_neq0].
Qed.

Lemma mpoly_sound m : peval (mpoly m) = aeval m.
Proof.
elim: m => [|[a k] m IH].
  by rewrite -[mpoly _]/(pconst 1) pconst_sound Q2F1.
rewrite -[mpoly _]/(pmul (ppow (patom a) k) (mpoly m)).
by rewrite pmul_sound ppow_sound patom_sound IH.
Qed.

Lemma pterm_sound t : peval (pterm t) = bound_interp F t.1 * aeval t.2.
Proof.
by rewrite /pterm pmul_sound pconst_sound -bound_interpE mpoly_sound.
Qed.

Local Arguments padd : simpl never.
Local Arguments pvar : simpl never.
Local Arguments pconst : simpl never.
Local Arguments pscale : simpl never.

Definition fsI (fs : seq fact) := forall f, List.In f fs -> kI f.1 (peval f.2).

Lemma fsI_cons f fs : kI f.1 (peval f.2) -> fsI fs -> fsI (f :: fs).
Proof. by move=> h1 h2 f' [<-|/h2]. Qed.

Lemma fsI_cat fs1 fs2 : fsI fs1 -> fsI fs2 -> fsI (fs1 ++ fs2).
Proof.
elim: fs1 => [|g fs1 IH] //= h1 h2 f [<-|h]; first by apply: h1; left.
by apply: IH h => // f' h'; apply: h1; right.
Qed.

Lemma low_fact_sound s b i :
  (if s then bound_interp F b < nth 0 env i
   else bound_interp F b <= nth 0 env i) ->
  kI (low_fact s b i).1 (peval (low_fact s b i).2).
Proof.
rewrite /= padd_sound pconst_sound patom_sound Q2F_opp -bound_interpE.
by case: s => /=; rewrite ?subr_gt0 ?subr_ge0.
Qed.

Lemma upp_fact_sound s b i :
  (if s then nth 0 env i < bound_interp F b
   else nth 0 env i <= bound_interp F b) ->
  kI (upp_fact s b i).1 (peval (upp_fact s b i).2).
Proof.
rewrite /= padd_sound pconst_sound pscale_sound patom_sound Q2Fm1 mulN1r.
by rewrite -bound_interpE; case: s => /=; rewrite ?subr_gt0 ?subr_ge0.
Qed.

Lemma csum_sound fs ls : fsI fs -> cpos fs ls ->
  0 <= peval (csum fs ls) /\ (cstrict fs ls -> 0 < peval (csum fs ls)).
Proof.
elim: fs ls => [|[k R] fs IH] [|l ls] //= H.
have hR : kI k (peval R) by apply: (H (k, R)); left.
have Hfs : fsI fs by move=> f h; apply: H; right.
case/andP => /andP [/Q2F_ge0b l0 hk] /(IH ls Hfs) [s0 s1].
rewrite padd_sound pscale_sound; clear H IH.
have t0 : 0 <= Q2F l * peval R.
  case/orP: hk => [/qzP ->|]; first by rewrite mul0r.
  by case: k hR => //= hR _; rewrite mulr_ge0 // ltW.
split; first exact: addr_ge0.
case/orP => [|/s1 h]; last by rewrite ltr_wpDl.
case: k hR {t0 hk} => //= hR /Q2F_gt0b l1.
by rewrite ltr_pwDl // mulr_gt0.
Qed.

Lemma comb_check_sound fs strict P ls c0 : fsI fs ->
  comb_check fs strict P ls c0 ->
  if strict then 0 < peval P else 0 <= peval P.
Proof.
move=> H /and4P [hp /Q2F_ge0b c00 /peqb_sound -> hs].
have [s0 s1] := csum_sound H hp.
rewrite padd_sound pconst_sound; case: strict hs => /= [/orP []|_].
- by move/Q2F_gt0b => c01; rewrite ltr_wpDl.
- by move/s1 => h; rewrite ltr_pwDl.
exact: addr_ge0.
Qed.

Lemma msplit_sound (P : pred poly) p :
  (forall q, P q -> peval q != 0) -> all P (msplit p) -> peval p != 0.
Proof.
move=> H; case: p => [|[c m] [|t p]] /=; rewrite ?andbT; try exact: H.
case/andP => /H; rewrite pconst_sound addr0 => c0 Hm.
rewrite mulf_neq0 //; elim: m Hm => [|[a k] m IH] /=.
  by rewrite oner_neq0.
case/andP => /H; rewrite patom_sound => a0 /IH m0.
by rewrite mulf_neq0 // expf_neq0.
Qed.

Lemma nzf_sound (P : pred poly) e :
  (forall q, P q -> peval q != 0) -> all P (nzf e) -> ri e != 0.
Proof.
move=> H.
have D e' : all P (msplit (pnorm e')) -> ri e' != 0.
  by move/(msplit_sound H); rewrite pnorm_sound.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|
            e1 IH1 k|e1 IH1]; try exact: D.
- by move/IH1; rewrite /= oppr_eq0.
- by rewrite /= all_cat => /andP [/IH1 h1 /IH2 h2]; rewrite mulf_neq0.
- by move/IH1 => h; rewrite /= expf_neq0.
by move/IH1; rewrite /= invr_eq0.
Qed.

End CheckProofs.
