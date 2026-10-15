(******************************************************************************)
(* Denest: denesting of depth-two square roots (M19, phase 1).                *)
(*   sqrt (a + b sqrt c) = sqrt ((a + d) / 2) + sign b * sqrt ((a - d) / 2)   *)
(*   when a ^ 2 - b ^ 2 c = d ^ 2 is the square of a rational d >= 0.         *)
(* Candidate finder (unverified computation, RadcanZ):                        *)
(*   read_quad p      == (a, b, c) when the normal form p is a + b * sqrt c   *)
(*   denest_cand a b c == the candidate (den, [:: (z_i, n_i)]) meaning        *)
(*                       (sum_i z_i * sqrt n_i) / den                         *)
(*   denest_find e    == the candidate for the radicand e, if any             *)
(*   dc_sum ts, dc_rexpr c == the candidate as an rexpr                       *)
(* Sign certificate (verified):                                               *)
(*   sq_lower D z n   == a lower bound of D * z * sqrt n, D > 0: z * s with   *)
(*                       s = Z.sqrt (n D ^ 2) (z >= 0) or s or s + 1 (z < 0), *)
(*                       the bound checked by integer arithmetic              *)
(*   sq_nonneg ts     == sum_i z_i * sqrt n_i >= 0, found with D = 2 ^ k      *)
(*   sq_nonneg_sound  : sq_nonneg ts -> 0 <= \sum_i Z2F z_i * proot r 2 n_i   *)
(* Denesting (verified):                                                      *)
(*   denest_ok e c    == radcan_check (dc_rexpr c ^+ 2) e = Some [::] and     *)
(*                       sq_nonneg c.2                                        *)
(*   denest_sound     : denest_ok e c -> proot 2 e = dc_rexpr c (rinterp r)   *)
(*   denest_root n a  == the checked candidate of proot n a (n = 2), if any   *)
(*   denest_rw e      == every RRootE 2 a of e (inner ones first) replaced by *)
(*                       its checked candidate                                *)
(*   denest_rw_sound  : rinterp r env (denest_rw e) = rinterp r env e         *)
(*   radcan_check_denest e1 e2 == radcan_check (denest_rw e1) (denest_rw e2)  *)
(*   radcan_eq_denest : radcan_check_denest e1 e2 = Some cs                   *)
(*                      -> all_conds r env cs -> rinterp e1 = rinterp e2      *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Radcan.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Candidate finder: unverified *)

Definition z_sqrt_exact (z : Z) : option Z :=
  let s := Z.sqrt z in if Z.eqb (Z.mul s s) z then Some s else None.

Definition q_sqrt_exact (q : Q) : option Q :=
  let q := Qred q in
  if Z.ltb (Qnum q) 0 then None else
  match z_sqrt_exact (Qnum q), z_sqrt_exact (Zpos (Qden q)) with
  | Some n, Some (Zpos d) => Some (Qmake n d)
  | _, _ => None
  end.

(* a monomial made of square roots of primes: the product of the primes *)
Definition mono_sqrt (m : mono) : option positive :=
  foldr (fun f acc =>
           if acc is Some c then
             let: (b, n, e) := f in
             if (n == 2)%N && (e == 1)%N then Some (Pos.mul b c) else None
           else None) (Some 1%positive) m.

Fixpoint read_quad_rec (p : nf) (a : Q) (bc : option (Q * positive)) :
  option (Q * Q * positive) :=
  match p with
  | [::] => if bc is Some (b, c) then Some (a, b, c) else None
  | (q, (v, m)) :: p' =>
    if v is [::] then
      if m is [::] then read_quad_rec p' (Qplus a (ZNum.c_to_Q q)) bc
      else match bc, mono_sqrt m with
           | None, Some c => read_quad_rec p' a (Some (ZNum.c_to_Q q, c))
           | _, _ => None
           end
    else None
  end.

Definition read_quad (p : nf) : option (Q * Q * positive) :=
  read_quad_rec p (Qmake Z0 1) None.

(* (den, [:: (z_i, n_i)]) is (sum_i z_i * sqrt n_i) / den *)
Definition dcand := (positive * seq (Z * positive))%type.

Definition denest_cand (a b : Q) (c : positive) : option dcand :=
  if Qle_bool a (Qmake Z0 1) then None else
  let two := Qmake 2 1 in
  if q_sqrt_exact (Qminus (Qmult a a) (Qmult (Qmult b b) (Qmake (Zpos c) 1)))
  is Some d then
    let x := Qred (Qdiv (Qplus a d) two) in
    let y := Qred (Qdiv (Qminus a d) two) in
    let xd := Qden x in let yd := Qden y in
    let s := if Qle_bool (Qmake Z0 1) b then Zpos xd else Zneg xd in
    match Qnum x, Qnum y with
    | Zpos xn, Zpos yn =>
      Some ((xd * yd)%positive, [:: (Zpos yd, (xn * xd)%positive);
                                     (s, (yn * yd)%positive)])
    | Zpos xn, Z0 =>
      Some ((xd * yd)%positive, [:: (Zpos yd, (xn * xd)%positive)])
    | _, _ => None
    end
  else None.

Definition denest_find (e : rexpr) : option dcand :=
  if read_quad (radcan_nf MStd e e).1.1 is Some (a, b, c) then
    denest_cand a b c
  else None.

Fixpoint dc_sum (ts : seq (Z * positive)) : rexpr :=
  match ts with
  | [::] => RCst Z0
  | (z, n) :: ts' => RAdd (RMul (RCst z) (RRoot 2 n)) (dc_sum ts')
  end.

Definition dc_rexpr (c : dcand) : rexpr :=
  RMul (dc_sum c.2) (RInv (RCst (Zpos c.1))).

(* Sign certificate *)

(* a lower bound of z * (D * sqrt n), checked *)
Definition sq_lower (D z : Z) (n : positive) : option Z :=
  let N := Z.mul (Zpos n) (Z.mul D D) in
  let s := Z.sqrt N in
  if Z.leb 0 z then
    if Z.leb 0 s && Z.leb (Z.mul s s) N then Some (Z.mul z s) else None
  else
    let u := if Z.eqb (Z.mul s s) N then s else Z.succ s in
    if Z.leb 0 u && Z.leb N (Z.mul u u) then Some (Z.mul z u) else None.

Fixpoint sq_lsum (D : Z) (ts : seq (Z * positive)) : option Z :=
  match ts with
  | [::] => Some Z0
  | (z, n) :: ts' =>
    match sq_lower D z n, sq_lsum D ts' with
    | Some v, Some w => Some (Z.add v w)
    | _, _ => None
    end
  end.

Definition sq_check_at (D : Z) (ts : seq (Z * positive)) : bool :=
  if Z.ltb 0 D then
    if sq_lsum D ts is Some v then Z.leb 0 v else false
  else false.

Fixpoint sq_search (fuel : nat) (D : Z) (ts : seq (Z * positive)) : bool :=
  match fuel with
  | O => false
  | S f => if sq_check_at D ts then true else sq_search f (Z.mul D 2) ts
  end.

(* precisions 1, 1/2, ..., 1/2^63 *)
Definition sq_nonneg (ts : seq (Z * positive)) : bool := sq_search 64 1 ts.

(* the verified denesting step *)
Definition denest_ok (e : rexpr) (c : dcand) : bool :=
  if radcan_check (RPow (dc_rexpr c) 2) e is Some [::] then sq_nonneg c.2
  else false.

Definition denest1 (e : rexpr) : option rexpr :=
  if denest_find e is Some c then
    if denest_ok e c then Some (dc_rexpr c) else None
  else None.

Definition denest_root (n : positive) (a : rexpr) : rexpr :=
  if Pos.eqb n 2 then (if denest1 a is Some c then c else RRootE n a)
  else RRootE n a.

Arguments denest_root : simpl never.

Fixpoint denest_rw (e : rexpr) : rexpr :=
  match e with
  | RRootE n a => denest_root n (denest_rw a)
  | RAdd a b => RAdd (denest_rw a) (denest_rw b)
  | ROpp a => ROpp (denest_rw a)
  | RSub a b => RSub (denest_rw a) (denest_rw b)
  | RMul a b => RMul (denest_rw a) (denest_rw b)
  | RPow a k => RPow (denest_rw a) k
  | RInv a => RInv (denest_rw a)
  | RCst _ | RVar _ | RRoot _ _ => e
  end.

(* Phase 3: radicands with variables, A + B * s with s a product of square
   root atoms, s ^ 2 = C; candidate finder unverified *)

Definition is_sqrt_atom (a : atom) : bool :=
  if a is ARoot n _ then Pos.eqb n 2 else false.

Definition vhalf (v : vmono) : option vmono :=
  if all (fun ak => ~~ odd ak.2) v then
    Some (map (fun ak => (ak.1, (ak.2 %/ 2)%N)) v)
  else None.

(* exact square root d of D: d = c0 * v0 + ..., the next term of d is the
   leading term of D - d ^ 2 divided by 2 * c0 * v0 (graded order) *)
Fixpoint psqrt_loop (fuel : nat) (D d : nf) (c0 : coef) (v0 : vmono) :
  option nf :=
  match fuel with
  | O => None
  | S f =>
    let R := psub D (nf_mul d d) in
    if R is [::] then Some d else
    match lead R with
    | Some (c, v) =>
      if vdiv v v0 is Some u then
        let t := nf_single (ZNum.c_div c (ZNum.c_mul (ZNum.c_of_Z 2) c0))
                           (u, [::]) in
        psqrt_loop f D (nf_add d t) c0 v0
      else None
    | None => None
    end
  end.

Definition psqrt (D : nf) : option nf :=
  if D is [::] then Some [::] else
  if ~~ ispoly D then None else
  match lead D with
  | Some (c, v) =>
    match q_sqrt_exact (ZNum.c_to_Q c), vhalf v with
    | Some s, Some u =>
      let s := Qred s in psqrt_loop 64 D (nf_single s (u, [::])) s u
    | _, _ => None
    end
  | None => None
  end.

(* p = A + B * s: A without square root atom, s the common product of the
   square root atoms (exponent 1) of the other terms *)
Fixpoint read_qv (p : nf) (A B : nf) (s : option vmono) :
  option (nf * nf * vmono) :=
  match p with
  | [::] => if s is Some w then Some (A, B, w) else None
  | (q, (v, m)) :: p' =>
    if m is [::] then
      let rv := filter (fun ak => is_sqrt_atom ak.1) v in
      let w := filter (fun ak => ~~ is_sqrt_atom ak.1) v in
      let t := [:: (q, (w, [::]))] in
      if rv is [::] then read_qv p' (nf_add A t) B s
      else if ~~ all (fun ak => ak.2 == 1%N) rv then None
      else match s with
           | None => read_qv p' A (nf_add B t) (Some rv)
           | Some rv' => if cmp_eqb (vmono_cmp rv rv') then
                           read_qv p' A (nf_add B t) s
                         else None
           end
    else None
  end.

(* C = s ^ 2, the product of the radicands *)
Definition sqrt_rad (w : vmono) : nf :=
  foldr (fun ak acc => if ak.1 is ARoot _ e then nf_mul (RadcanZ.pnorm e) acc
                       else acc) nf_one w.

Definition half_nf (p : nf) : nf := nf_mul [:: (Qmake 1 2, ([::], [::]))] p.

(* sqrt P, printed as p when P = p ^ 2 *)
Definition sqrt_nf (P : nf) : rexpr :=
  if psqrt P is Some p then nf_to_rexpr p else RRootE 2 (nf_to_rexpr P).

(* the candidate sqrt P +- sqrt Q, P = (A + d) / 2, Q = (A - d) / 2, d ^ 2 =
   A ^ 2 - B ^ 2 C, d with a positive leading coefficient; the sign is the
   sign of B when B is constant, + otherwise *)
Definition denest_findv (e : rexpr) : option rexpr :=
  if read_qv (radcan_nf MStd e e).1.1 [::] [::] None is Some (A, B, w) then
    let D := psub (nf_mul A A) (nf_mul (nf_mul B B) (sqrt_rad w)) in
    if psqrt D is Some d then
      let P := half_nf (nf_add A d) in
      let Q := half_nf (psub A d) in
      if P is [::] then None else if Q is [::] then None else
      let sP := sqrt_nf P in let sQ := sqrt_nf Q in
      if const_of B is Some b then
        Some (if Qle_bool (Qmake 0 1) (ZNum.c_to_Q b) then RAdd sP sQ
              else RSub sP sQ)
      else Some (RAdd sP sQ)
    else None
  else None.

(* sufficient conditions for 0 <= e (verified): sums and products of
   nonnegative constants, variables and roots, u - v with u, v square roots
   or nonnegative constants (then u ^ 2 - v ^ 2 >= 0) *)
Definition ge0c (a : rexpr) : seq cond :=
  if a is RCst z then (if Z.leb 0 z then [::] else [:: CGe0 a])
  else [:: CGe0 a].

(* e ^ 2 when e is a square root or a nonnegative constant *)
Definition sqv (e : rexpr) : option rexpr :=
  match e with
  | RRootE n a => if Pos.eqb n 2 then Some a else None
  | RCst z => if Z.leb 0 z then Some (RCst (Z.mul z z)) else None
  | _ => None
  end.

Fixpoint nn_conds (e : rexpr) : option (seq cond) :=
  match e with
  | RCst z => if Z.leb 0 z then Some [::] else None
  | RRoot _ _ => Some [::]
  | RRootE _ a => Some (ge0c a)
  | RAdd a b | RMul a b =>
    match nn_conds a, nn_conds b with
    | Some c1, Some c2 => Some (c1 ++ c2)
    | _, _ => None
    end
  | RInv a => nn_conds a
  | RVar _ => Some [:: CGe0 e]
  | RSub a b =>
    match sqv a, sqv b, nn_conds a, nn_conds b with
    | Some a2, Some b2, Some c1, Some c2 =>
      Some (c1 ++ c2 ++ [:: CGe0 (RSub a2 b2)])
    | _, _, _, _ => None
    end
  | _ => None
  end.

Definition nnc (e : rexpr) : seq cond :=
  if nn_conds e is Some cs then cs else [:: CGe0 e].

(* the checked candidate and its conditions *)
Definition denestv (e : rexpr) : option (rexpr * seq cond) :=
  if denest_findv e is Some c then
    if radcan_check (RPow c 2) e is Some cs then Some (c, cdedup (cs ++ nnc c))
    else None
  else None.

(* constants first (no condition), then variables *)
Definition denest_rootc (n : positive) (a : rexpr) : rexpr * seq cond :=
  if Pos.eqb n 2 then
    if denest1 a is Some c then (c, [::])
    else if denestv a is Some cc then cc else (RRootE n a, [::])
  else (RRootE n a, [::]).

Arguments denest_rootc : simpl never.

Fixpoint denest_rwc (e : rexpr) : rexpr * seq cond :=
  match e with
  | RRootE n a =>
    let: (a', c1) := denest_rwc a in
    let: (b, c2) := denest_rootc n a' in (b, c1 ++ c2)
  | RAdd a b =>
    let: (a', c1) := denest_rwc a in
    let: (b', c2) := denest_rwc b in (RAdd a' b', c1 ++ c2)
  | ROpp a => let: (a', c1) := denest_rwc a in (ROpp a', c1)
  | RSub a b =>
    let: (a', c1) := denest_rwc a in
    let: (b', c2) := denest_rwc b in (RSub a' b', c1 ++ c2)
  | RMul a b =>
    let: (a', c1) := denest_rwc a in
    let: (b', c2) := denest_rwc b in (RMul a' b', c1 ++ c2)
  | RPow a k => let: (a', c1) := denest_rwc a in (RPow a' k, c1)
  | RInv a => let: (a', c1) := denest_rwc a in (RInv a', c1)
  | RCst _ | RVar _ | RRoot _ _ => (e, [::])
  end.

Definition radcan_check_denest (e1 e2 : rexpr) : option (seq cond) :=
  let: (e1', c1) := denest_rwc e1 in
  let: (e2', c2) := denest_rwc e2 in
  if radcan_check e1' e2' is Some cs then Some (cdedup (c1 ++ c2 ++ cs))
  else None.

Local Open Scope ring_scope.

Section DenestSound.

Variables (F : numFieldType) (r : posroot F).

Implicit Types (a l u : F).

Lemma proot2_lb a l : 0 <= l -> l ^+ 2 <= a -> l <= proot r 2 a.
Proof.
move=> l0 la; have a0 : 0 <= a by rewrite (le_trans _ la) ?exprn_ge0.
by rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?proot_ge0 ?prootK.
Qed.

Lemma proot2_ub a u : 0 <= a -> 0 <= u -> a <= u ^+ 2 -> proot r 2 a <= u.
Proof.
move=> a0 u0 au.
by rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?proot_ge0 ?prootK.
Qed.

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

(* D * sqrt n = sqrt (n * D ^ 2) *)
Lemma sq_scale (D : Z) (n : positive) : Z.lt 0 D ->
  Z2F F D * proot r 2 (pos2F F n) =
  proot r 2 (Z2F F (Z.mul (Zpos n) (Z.mul D D))).
Proof.
move=> D0; have D0' := ltW (Z2F_gt0z D0).
apply/esym/proot_eq => //; first by rewrite mulr_ge0 ?proot_ge0 ?pos2F_ge0.
by rewrite exprMn prootK ?pos2F_ge0 // !Z2F_mul /= mulrC expr2.
Qed.

Lemma sq_lower_sound D z n v : Z.lt 0 D -> sq_lower D z n = Some v ->
  Z2F F v <= Z2F F z * (Z2F F D * proot r 2 (pos2F F n)).
Proof.
move=> D0; rewrite sq_scale // /sq_lower.
set N := Z.mul _ _; set s := Z.sqrt N.
have N0 : 0 <= Z2F F N.
  by apply: Z2F_ge0z; rewrite /N; have := Z.square_nonneg D; lia.
case: (Z.leb_spec 0 z) => z0.
  case: (Z.leb_spec 0 s) => //= s0; case: (Z.leb_spec (Z.mul s s) N) => //.
  move=> ssN [<-]; rewrite Z2F_mul ler_wpM2l ?Z2F_ge0z //.
  by apply: proot2_lb; rewrite ?Z2F_ge0z // expr2 -Z2F_mul Z2F_lez.
set u := if Z.eqb (Z.mul s s) N then s else Z.succ s.
case: (Z.leb_spec 0 u) => //= u0; case: (Z.leb_spec N (Z.mul u u)) => //.
move=> Nuu [<-]; rewrite Z2F_mul ler_wnM2l //.
  by apply: (Z2F_lez (y := Z0)); lia.
apply: proot2_ub => //; first exact: Z2F_ge0z.
by rewrite expr2 -Z2F_mul Z2F_lez.
Qed.

Definition sq_val (ts : seq (Z * positive)) : F :=
  \sum_(t <- ts) Z2F F t.1 * proot r 2 (pos2F F t.2).

Lemma sq_lsum_sound D ts v : Z.lt 0 D -> sq_lsum D ts = Some v ->
  Z2F F v <= Z2F F D * sq_val ts.
Proof.
move=> D0; elim: ts v => [|[z n] ts IH] v /=.
  by case=> <-; rewrite /sq_val big_nil mulr0.
case E1 : (sq_lower D z n) => [v1|] //; case E2 : (sq_lsum D ts) => [w|] //.
case=> <-; rewrite /sq_val big_cons mulrDr Z2F_add lerD //; last exact: IH.
by rewrite mulrCA; exact: sq_lower_sound.
Qed.

Lemma sq_check_at_sound D ts : sq_check_at D ts -> 0 <= sq_val ts.
Proof.
rewrite /sq_check_at; case: (Z.ltb_spec 0 D) => // D0.
case E : (sq_lsum D ts) => [v|] // /Z.leb_le v0.
have := le_trans (Z2F_ge0z v0) (sq_lsum_sound D0 E).
by rewrite pmulr_rge0 // Z2F_gt0z.
Qed.

Lemma sq_search_sound k D ts : sq_search k D ts -> 0 <= sq_val ts.
Proof.
elim: k D => [|k IH] D //=; case E : (sq_check_at D ts) => H.
  exact: sq_check_at_sound E.
exact: IH H.
Qed.

Theorem sq_nonneg_sound ts : sq_nonneg ts ->
  0 <= \sum_(t <- ts) Z2F F t.1 * proot r 2 (pos2F F t.2).
Proof. exact: sq_search_sound. Qed.

Lemma dc_sum_val env ts : rinterp r env (dc_sum ts) = sq_val ts.
Proof.
rewrite /sq_val; elim: ts => [|[z n] ts IH] /=; first by rewrite big_nil.
by rewrite big_cons IH.
Qed.

Lemma dc_rexpr_ge0 env c : sq_nonneg c.2 -> 0 <= rinterp r env (dc_rexpr c).
Proof.
case: c => D ts /= /sq_nonneg_sound H; rewrite dc_sum_val.
by rewrite mulr_ge0 // invr_ge0 pos2F_ge0.
Qed.

Theorem denest_sound env e c : denest_ok e c ->
  rinterp r env (RRootE 2 e) = rinterp r env (dc_rexpr c).
Proof.
rewrite /denest_ok; case E : (radcan_check _ e) => [[|? ?]|] // H.
apply: proot_eq => //; first exact: dc_rexpr_ge0.
by have /= -> := radcan_eq r env E.
Qed.

Lemma denest1_sound env e c : denest1 e = Some c ->
  rinterp r env c = rinterp r env (RRootE 2 e).
Proof.
rewrite /denest1; case: (denest_find e) => [c'|] //.
by case E : (denest_ok e c') => // -[<-]; rewrite (denest_sound env E).
Qed.

Theorem denest_rw_sound env e : rinterp r env (denest_rw e) = rinterp r env e.
Proof.
elim: e => //= [n a IH|a IHa b IHb|a IH|a IHa b IHb|a IHa b IHb|a IH k|a IH].
- rewrite -IH /denest_root; case: (Pos.eqb_spec n 2) => [->|//].
  by case E : (denest1 (denest_rw a)) => [c|] //; exact: denest1_sound.
- by rewrite IHa IHb.
- by rewrite IH.
- by rewrite IHa IHb.
- by rewrite IHa IHb.
- by rewrite IH.
by rewrite IH.
Qed.

Theorem radcan_eq_denest env e1 e2 cs :
  radcan_check_denest e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hc; rewrite -[LHS](denest_rw_sound env) -[RHS](denest_rw_sound env).
exact: radcan_eq_cond H Hc.
Qed.

End DenestSound.
