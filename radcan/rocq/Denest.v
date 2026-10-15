(******************************************************************************)
(* Denest: denesting of depth-two square roots (M19, phases 1, 3, 4, 5).      *)
(*   sqrt (a + b sqrt c) = sqrt ((a + d) / 2) + sign b * sqrt ((a - d) / 2)   *)
(*   when a ^ 2 - b ^ 2 c = d ^ 2 is the square of a rational d >= 0.         *)
(* Phase 1, constants. Candidate finder (unverified computation, RadcanZ):    *)
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
(*   denest1 e        == the checked candidate of proot 2 e: denest_find,     *)
(*                       then denest_findm (phase 4)                          *)
(*   denest_root n a  == the checked candidate of proot n a (n = 2), if any   *)
(*   denest_rw e      == every RRootE 2 a of e (inner ones first) replaced by *)
(*                       its checked candidate                                *)
(*   denest_rw_sound  : rinterp r env (denest_rw e) = rinterp r env e         *)
(* Phase 4, several roots. Candidate finder (unverified):                     *)
(*   read_multi p     == (a0, [:: (b_j, m_j)], bases) when p is               *)
(*                       a0 + sum_j b_j * sqrt m_j                            *)
(*   pxor p q         == p q / g ^ 2, g = gcd p q: sqrt p sqrt q =            *)
(*                       g * sqrt (pxor p q)                                  *)
(*   mcands k bs ts   == the sets {p_1, ..., p_k}: p_1 a product of bases,    *)
(*                       p_j = pxor p_1 m (m a root of the radicand)          *)
(*   msolve ts ps     == the c_i: c_i c_j = b / (2 gcd p_i p_j), b the        *)
(*                       coefficient of sqrt (pxor p_i p_j),                  *)
(*                       c_1 ^ 2 = c_1 c_2 * c_1 c_3 / (c_2 c_3)              *)
(*   mcheck a0 ts cs  == (sum_i c_i sqrt p_i) ^ 2 is the radicand (distinct   *)
(*                       pxor, every cross term, a0 = sum_i c_i ^ 2 p_i)      *)
(*   denest_findm e   == the first checked set, k (k - 1) / 2 roots in e,     *)
(*                       3 <= k <= 5, at most 6 bases; sign by sq_nonneg      *)
(* Phase 3, variables. Candidate finder (unverified):                         *)
(*   psqrt D          == exact square root of the polynomial D (graded order) *)
(*   read_qv p        == (A, B, s): the normal form p is A + B * s, s a       *)
(*                       product of square root atoms, A, B without them      *)
(*   denest_findv e   == sqrt P +- sqrt Q, P, Q = (A +- d) / 2, d ^ 2 =       *)
(*                       A ^ 2 - B ^ 2 s ^ 2 (sign of B, + if B not constant; *)
(*                       sqrt P printed p when P = p ^ 2)                     *)
(* Conditions (verified):                                                     *)
(*   nn_conds e       == Some cs, cs sufficient for 0 <= e: sums, products of *)
(*                       nonneg constants, variables, roots (radicand >= 0),  *)
(*                       u - v, u and v roots or constants (u^2 - v^2 >= 0)   *)
(*   nnc e            == nn_conds e, or [:: CGe0 e]                           *)
(* Phase 5, several roots with variables. Candidate finder (unverified):      *)
(*   read_mv p A ts   == (A, [:: (s_j, B_j)]): p = A + sum_j B_j * s_j, s_j   *)
(*                       distinct products of square root atoms, A, B_j       *)
(*                       without them                                         *)
(*   vxor w1 w2       == (s, g): w1 w2 = g ^ 2 s, s the symmetric difference  *)
(*   vmcands k U ts   == the sets {w_1, ..., w_k}: w_1 a product of atoms of  *)
(*                       U, w_j = s of vxor w_1 s_j                           *)
(*   vmsolve ts ws    == the polynomials c_i: c_i c_j = B / (2 g ^ 2), B the  *)
(*                       coefficient of s, (s, g) = vxor w_i w_j (pdiv),      *)
(*                       c_1 ^ 2 = c_1 c_2 * c_1 c_3 / c_2 c_3 (psqrt)        *)
(*   vmcheck A ts cs  == (sum_i c_i w_i) ^ 2 is the radicand, exactly         *)
(*   vcand cs         == the candidate, most leading coefficients positive    *)
(*   denest_findvm e  == the first checked set, k (k - 1) / 2 products s_j,   *)
(*                       3 <= k <= 5, at most 6 atoms                         *)
(*   denestv_try e oc == Some (c, cs): c = oc checked by radcan_check         *)
(*                       (c ^+ 2) e, cs its conditions and nnc c              *)
(*   denestv e        == denestv_try with denest_findv (phase 3), then with   *)
(*                       denest_findvm (phase 5)                              *)
(*   denestv_eq       : denestv e = Some (c, cs) -> all_conds r env cs ->     *)
(*                      proot r 2 (rinterp r env e) = rinterp r env c         *)
(*   denest_rwc e     == (e', cs): every RRootE 2 a of e (inner ones first)   *)
(*                       denested, constants first (phases 1, 4), then        *)
(*                       denestv (phases 3, 5)                                *)
(*   denest_rwc_sound : holds cs -> rinterp r env e' = rinterp r env e        *)
(*   radcan_check_denest e1 e2 == radcan_check on the denest_rwc sides, the   *)
(*                       conditions of both rewritings added                  *)
(*   radcan_eq_denest : radcan_check_denest e1 e2 = Some cs                   *)
(*                      -> all_conds r env cs -> rinterp e1 = rinterp e2      *)
(*   radcan_eq_denest_refined, denestv_eq_refined == the same with the        *)
(*                      conditions refined by Refine.v (refine cs = rcs)      *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Radcan Refine.
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

(* Phase 4: radicands a0 + sum_j b_j * sqrt m_j with several roots;
   candidate finder unverified *)

(* (a0, [:: (b_j, m_j)], bases of the roots) *)
Fixpoint read_multi_rec (p : nf) (a : Q) (ts : seq (Q * positive))
  (bs : seq positive) : option (Q * seq (Q * positive) * seq positive) :=
  match p with
  | [::] => Some (a, ts, bs)
  | (q, (v, m)) :: p' =>
    if v is [::] then
      if m is [::] then read_multi_rec p' (Qplus a (ZNum.c_to_Q q)) ts bs
      else if mono_sqrt m is Some c then
        let bs' := foldr (fun f acc => let: (b, _, _) := f in
                            if has (Pos.eqb b) acc then acc else b :: acc)
                         bs m in
        read_multi_rec p' a ((ZNum.c_to_Q q, c) :: ts) bs'
      else None
    else None
  end.

Definition read_multi (p : nf) :
  option (Q * seq (Q * positive) * seq positive) :=
  read_multi_rec p (Qmake Z0 1) [::] [::].

(* products of the subsets of bs *)
Fixpoint subprods (bs : seq positive) : seq positive :=
  if bs is b :: bs' then
    let s := subprods bs' in s ++ map (Pos.mul b) s
  else [:: 1%positive].

(* the k-subsets of l *)
Fixpoint choose (k : nat) (l : seq positive) : seq (seq positive) :=
  match k, l with
  | O, _ => [:: [::]]
  | S _, [::] => [::]
  | S k', x :: l' => map (cons x) (choose k' l') ++ choose k l'
  end.

Fixpoint pairs (T : Type) (l : seq T) : seq (T * T) :=
  if l is x :: l' then map (pair x) l' ++ pairs l' else [::].

(* sqrt p * sqrt q = g * sqrt m, g = gcd p q, m = p q / g ^ 2 *)
Definition pxor (p q : positive) : positive :=
  let g := Zpos (Pos.gcd p q) in
  Z.to_pos (Z.div (Z.mul (Zpos p) (Zpos q)) (Z.mul g g)).

Fixpoint qlook (m : positive) (ts : seq (Q * positive)) : option Q :=
  if ts is (b, n) :: ts' then
    if Pos.eqb m n then Some b else qlook m ts'
  else None.

Fixpoint puniq (l : seq positive) : bool :=
  if l is x :: l' then ~~ has (Pos.eqb x) l' && puniq l' else true.

(* beta p q == c_p * c_q, read from the term b * sqrt (pxor p q) *)
Definition mbeta (ts : seq (Q * positive)) (p q : positive) : Q :=
  if qlook (pxor p q) ts is Some b then
    Qdiv b (Qmake (Z.mul 2 (Zpos (Pos.gcd p q))) 1)
  else Qmake 0 1.

(* the coefficients: c_1 ^ 2 = beta_12 beta_13 / beta_23, c_j = beta_1j / c_1 *)
Definition msolve (ts : seq (Q * positive)) (ps : seq positive) :
  option (seq (Q * positive)) :=
  if ps is p1 :: ((p2 :: p3 :: _) as ps') then
    let c2 := Qdiv (Qmult (mbeta ts p1 p2) (mbeta ts p1 p3)) (mbeta ts p2 p3) in
    if q_sqrt_exact c2 is Some c1 then
      if Qeq_bool c1 (Qmake 0 1) then None else
      Some ((Qred c1, p1) ::
            map (fun p => (Qred (Qdiv (mbeta ts p1 p) c1), p)) ps')
    else None
  else None.

(* (sum_i c_i sqrt p_i) ^ 2 = a0 + sum_j b_j sqrt m_j, exactly *)
Definition mcheck (a0 : Q) (ts : seq (Q * positive))
  (cs : seq (Q * positive)) : bool :=
  let ps := pairs cs in
  (size ps == size ts) && puniq (map (fun x => pxor x.1.2 x.2.2) ps) &&
  all (fun x =>
         let: ((ci, pi), (cj, pj)) := x in
         if qlook (pxor pi pj) ts is Some b then
           Qeq_bool b (Qmult (Qmake (Z.mul 2 (Zpos (Pos.gcd pi pj))) 1)
                             (Qmult ci cj))
         else false) ps &&
  Qeq_bool a0 (foldr (fun x acc => Qplus (Qmult (Qmult x.1 x.1)
                                                  (Qmake (Zpos x.2) 1)) acc)
                     (Qmake 0 1) cs).

(* the candidate with a common denominator, sign chosen nonnegative *)
Definition mcand (cs : seq (Q * positive)) : dcand :=
  let D := foldr (fun x acc => Z.lcm (Zpos (Qden x.1)) acc) (Zpos 1) cs in
  let ts := map (fun x => (Z.mul (Qnum x.1) (Z.div D (Zpos (Qden x.1))), x.2))
                cs in
  let ts := if sq_nonneg ts then ts
            else map (fun x => (Z.opp x.1, x.2)) ts in
  (Z.to_pos D, ts).

Fixpoint first_some (A B : Type) (f : A -> option B) (l : seq A) : option B :=
  if l is x :: l' then (if f x is Some y then Some y else first_some f l')
  else None.

(* the candidate sets: p_1 a product of bases, the other p_j among the
   pxor p_1 m_j (so that pxor p_1 p_j is a root of the radicand) *)
Definition mcands (k : nat) (bs : seq positive) (ts : seq (Q * positive)) :
  seq (seq positive) :=
  flatten (map (fun p1 => map (cons p1)
                 (choose k.-1 (map (fun t => pxor p1 t.2) ts)))
               (subprods bs)).

(* k terms when the radicand has k (k - 1) / 2 roots, 3 <= k <= 5, at most
   6 bases *)
Definition denest_findm (e : rexpr) : option dcand :=
  if read_multi (radcan_nf MStd e e).1.1 is Some (a0, ts, bs) then
    if (6 < size bs)%N then None else
    let T := size ts in
    let k := (if T == 3 then 3 else if T == 6 then 4
              else if T == 10 then 5 else 0)%N in
    if k == 0%N then None else
    first_some (fun ps => if msolve ts ps is Some cs then
                            if mcheck a0 ts cs then Some (mcand cs) else None
                          else None)
               (mcands k bs ts)
  else None.

(* the verified denesting step *)
Definition denest_ok (e : rexpr) (c : dcand) : bool :=
  if radcan_check (RPow (dc_rexpr c) 2) e is Some [::] then sq_nonneg c.2
  else false.

Definition denest_try (e : rexpr) (oc : option dcand) : option rexpr :=
  if oc is Some c then
    if denest_ok e c then Some (dc_rexpr c) else None
  else None.

(* one square root (phase 1), then several (phase 4) *)
Definition denest1 (e : rexpr) : option rexpr :=
  if denest_try e (denest_find e) is Some c then Some c
  else denest_try e (denest_findm e).

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

(* Phase 5: several square roots with variables, A + sum_j B_j * s_j with
   s_j distinct products of square root atoms; candidate finder unverified *)

Definition vset (w : vmono) : vmono := map (fun ak => (ak.1, 1%N)) w.

Fixpoint vlook (w : vmono) (ts : seq (vmono * nf)) : option nf :=
  if ts is (w', B) :: ts' then
    if cmp_eqb (vmono_cmp w w') then Some B else vlook w ts'
  else None.

Fixpoint vupd (w : vmono) (t : nf) (ts : seq (vmono * nf)) :
  seq (vmono * nf) :=
  if ts is (w', B) :: ts' then
    if cmp_eqb (vmono_cmp w w') then (w', nf_add B t) :: ts'
    else (w', B) :: vupd w t ts'
  else [:: (w, t)].

(* (A, [:: (s_j, B_j)]) *)
Fixpoint read_mv (p : nf) (A : nf) (ts : seq (vmono * nf)) :
  option (nf * seq (vmono * nf)) :=
  match p with
  | [::] => Some (A, ts)
  | (q, (v, m)) :: p' =>
    if m is [::] then
      let rv := filter (fun ak => is_sqrt_atom ak.1) v in
      let w := filter (fun ak => ~~ is_sqrt_atom ak.1) v in
      let t := [:: (q, (w, [::]))] in
      if rv is [::] then read_mv p' (nf_add A t) ts
      else if all (fun ak => ak.2 == 1%N) rv then read_mv p' A (vupd rv t ts)
      else None
    else None
  end.

(* the subsets of the atoms of U *)
Fixpoint vsubsets (U : vmono) : seq vmono :=
  if U is a :: U' then
    let s := vsubsets U' in s ++ map (vmono_mul [:: a]) s
  else [:: [::]].

Fixpoint vchoose (k : nat) (l : seq vmono) : seq (seq vmono) :=
  match k, l with
  | O, _ => [:: [::]]
  | S _, [::] => [::]
  | S k', x :: l' => map (cons x) (vchoose k' l') ++ vchoose k l'
  end.

(* w1 w2 = g ^ 2 * x: (x, g), x the symmetric difference, g the common atoms *)
Definition vxor (w1 w2 : vmono) : vmono * vmono :=
  let u := vmono_mul w1 w2 in
  (filter (fun ak => ak.2 == 1%N) u, vset (filter (fun ak => ak.2 == 2%N) u)).

Definition two_nf : nf := nf_single (ZNum.c_of_Z 2) ([::], [::]).

(* c_i c_j, read from the term B * x of x = vxor w_i w_j: B / (2 g ^ 2) *)
Definition vbeta (ts : seq (vmono * nf)) (wi wj : vmono) : option nf :=
  let: (x, g) := vxor wi wj in
  if vlook x ts is Some B then pdiv B (nf_mul two_nf (sqrt_rad g)) else None.

Fixpoint omap_seq (A B : Type) (f : A -> option B) (l : seq A) :
  option (seq B) :=
  if l is x :: l' then
    match f x, omap_seq f l' with
    | Some y, Some s => Some (y :: s)
    | _, _ => None
    end
  else Some [::].

(* c_1 ^ 2 = c_1 c_2 * c_1 c_3 / c_2 c_3, c_j = c_1 c_j / c_1 *)
Definition vmsolve (ts : seq (vmono * nf)) (ws : seq vmono) :
  option (seq (nf * vmono)) :=
  if ws is w1 :: ((w2 :: w3 :: _) as ws') then
    match vbeta ts w1 w2, vbeta ts w1 w3, vbeta ts w2 w3 with
    | Some b12, Some b13, Some b23 =>
      if b23 is [::] then None else
      if pdiv (nf_mul b12 b13) b23 is Some c2 then
        if psqrt c2 is Some c1 then
          if c1 is [::] then None else
          let f w := if vbeta ts w1 w is Some b then
                       if pdiv b c1 is Some c then Some (c, w) else None
                     else None in
          if omap_seq f ws' is Some cs then Some ((c1, w1) :: cs) else None
        else None
      else None
    | _, _, _ => None
    end
  else None.

Fixpoint vuniq (l : seq vmono) : bool :=
  if l is x :: l' then
    ~~ has (fun y => cmp_eqb (vmono_cmp x y)) l' && vuniq l'
  else true.

(* (sum_i c_i w_i) ^ 2 is the radicand: distinct cross products, every
   cross term, A = sum_i c_i ^ 2 w_i ^ 2 *)
Definition vmcheck (A : nf) (ts : seq (vmono * nf)) (cs : seq (nf * vmono)) :
  bool :=
  let ps := pairs cs in
  (size ps == size ts) && vuniq (map (fun x => (vxor x.1.2 x.2.2).1) ps) &&
  all (fun x =>
         let: ((ci, wi), (cj, wj)) := x in
         let: (y, g) := vxor wi wj in
         if vlook y ts is Some B then
           nf_eqb B (nf_mul (nf_mul two_nf (sqrt_rad g)) (nf_mul ci cj))
         else false) ps &&
  nf_eqb A (foldr (fun x acc => nf_add (nf_mul (nf_mul x.1 x.1)
                                                (sqrt_rad x.2)) acc)
                  [::] cs).

(* the sign: most leading coefficients positive *)
Definition lead_pos (c : nf) : bool :=
  if lead c is Some (q, _) then ~~ Qle_bool (ZNum.c_to_Q q) (Qmake 0 1)
  else false.

Definition vcand (cs : seq (nf * vmono)) : rexpr :=
  let cs := if (size cs <= 2 * count (fun x => lead_pos x.1) cs)%N then cs
            else map (fun x => (nf_opp x.1, x.2)) cs in
  nf_to_rexpr (foldr (fun x acc =>
                        nf_add (nf_mul x.1 (nf_single ZNum.c_one (x.2, [::])))
                               acc) [::] cs).

(* the candidate sets: w_1 a product of atoms, the other w_j among the
   vxor w_1 s_j *)
Definition vmcands (k : nat) (U : vmono) (ts : seq (vmono * nf)) :
  seq (seq vmono) :=
  flatten (map (fun w1 => map (cons w1)
                 (vchoose k.-1 (map (fun t => (vxor w1 t.1).1) ts)))
               (vsubsets U)).

(* k terms when the radicand has k (k - 1) / 2 products of roots,
   3 <= k <= 5, at most 6 atoms *)
Definition denest_findvm (e : rexpr) : option rexpr :=
  if read_mv (radcan_nf MStd e e).1.1 [::] [::] is Some (A, ts) then
    let U := foldr (fun t acc => vset (vmono_mul t.1 acc)) [::] ts in
    if (6 < size U)%N then None else
    let T := size ts in
    let k := (if T == 3 then 3 else if T == 6 then 4
              else if T == 10 then 5 else 0)%N in
    if k == 0%N then None else
    first_some (fun ws => if vmsolve ts ws is Some cs then
                            if vmcheck A ts cs then Some (vcand cs) else None
                          else None)
               (vmcands k U ts)
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
Definition denestv_try (e : rexpr) (oc : option rexpr) :
  option (rexpr * seq cond) :=
  if oc is Some c then
    if radcan_check (RPow c 2) e is Some cs then Some (c, cdedup (cs ++ nnc c))
    else None
  else None.

(* one product of roots (phase 3), then several (phase 5) *)
Definition denestv (e : rexpr) : option (rexpr * seq cond) :=
  if denestv_try e (denest_findv e) is Some cc then Some cc
  else denestv_try e (denest_findvm e).

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
have T oc : denest_try e oc = Some c ->
    rinterp r env c = rinterp r env (RRootE 2 e).
  case: oc => [c'|] //; rewrite /denest_try.
  by case E : (denest_ok e c') => // -[<-]; rewrite (denest_sound env E).
rewrite /denest1; case E : (denest_try e (denest_find e)) => [c'|].
  by case=> E'; apply: (T (denest_find e)); rewrite E E'.
exact: T.
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

(* Phase 3: conditions *)

Lemma holds_all_conds env cs : holds r env cs -> all_conds r env cs.
Proof.
elim: cs => [|c cs IH] //= H; have [Hc /IH Hcs] := holds_cons H.
by case: cs {IH H} Hcs.
Qed.

Lemma holds1 env c : holds r env [:: c] -> cond_interp r env c.
Proof. by move=> H; apply: H; left. Qed.

Lemma ge0c_sound env t : holds r env (ge0c t) -> 0 <= rinterp r env t.
Proof.
case: t => [z|i|n p|n t|t t'|t|t t'|t t'|t k|t] /=; try exact: holds1.
by case: (Z.leb_spec 0 z) => z0 H; [exact: Z2F_ge0z | exact: holds1 H].
Qed.

Lemma sqv_sound env e e2 cs : sqv e = Some e2 -> nn_conds e = Some cs ->
  holds r env cs -> rinterp r env e ^+ 2 = rinterp r env e2.
Proof.
case: e => //= [z|n t].
  by case: (Z.leb_spec 0 z) => _ // [<-] _ _ /=; rewrite Z2F_mul expr2.
by case: n => // -[] // [<-] [<-] /ge0c_sound t0; rewrite prootK.
Qed.

Lemma pos_nat_gt0 (n : positive) : (0 < Pos.to_nat n)%N.
Proof. by apply/ssrnat.ltP; exact: Pos2Nat.is_pos. Qed.

Lemma nn_conds_sound env e cs : nn_conds e = Some cs -> holds r env cs ->
  0 <= rinterp r env e.
Proof.
elim: e cs => [z|i|n p|n a IHa|a IHa b IHb|a IHa|a IHa b IHb|a IHa b IHb|
               a IHa k|a IHa] cs //=.
- by case: (Z.leb_spec 0 z) => z0 // _ _; exact: Z2F_ge0z.
- by case=> <-; exact: holds1.
- by move=> _ _; rewrite proot_ge0 ?pos2F_ge0 ?pos_nat_gt0.
- by case=> <- /ge0c_sound a0; rewrite proot_ge0 ?pos_nat_gt0.
- case Ea : (nn_conds a) => [ca|] //; case Eb : (nn_conds b) => [cb|] //.
  by case=> <- /holds_cat [/(IHa _ Ea) a0 /(IHb _ Eb) b0]; rewrite addr_ge0.
- case Sa : (sqv a) => [a2|] //; case Sb : (sqv b) => [b2|] //.
  case Ea : (nn_conds a) => [ca|] //; case Eb : (nn_conds b) => [cb|] //.
  case=> <- /holds_cat [Ha /holds_cat [Hb /holds1 /=]].
  have a0 := IHa _ Ea Ha; have b0 := IHb _ Eb Hb.
  rewrite !subr_ge0 -(sqv_sound Sa Ea Ha) -(sqv_sound Sb Eb Hb) => H.
  by rewrite -(ler_pXn2r (n := 2)) ?nnegrE.
- case Ea : (nn_conds a) => [ca|] //; case Eb : (nn_conds b) => [cb|] //.
  by case=> <- /holds_cat [/(IHa _ Ea) a0 /(IHb _ Eb) b0]; rewrite mulr_ge0.
by move=> /IHa H /H; rewrite invr_ge0.
Qed.

Lemma nnc_sound env e : holds r env (nnc e) -> 0 <= rinterp r env e.
Proof.
rewrite /nnc; case E : (nn_conds e) => [cs|] H; last exact: holds1 H.
exact: nn_conds_sound E H.
Qed.

Lemma denestv_try_sound env e oc c cs : denestv_try e oc = Some (c, cs) ->
  holds r env cs -> rinterp r env (RRootE 2 e) = rinterp r env c.
Proof.
rewrite /denestv_try; case: oc => [c'|] //.
case E : (radcan_check _ e) => [cs'|] // -[<- <-].
move=> /holds_dedup /holds_cat [H1 H2].
apply: proot_eq => //; first exact: nnc_sound.
by have /= -> := radcan_eq_cond E (holds_all_conds H1).
Qed.

Theorem denestv_sound env e c cs : denestv e = Some (c, cs) ->
  holds r env cs -> rinterp r env (RRootE 2 e) = rinterp r env c.
Proof.
rewrite /denestv; case E : (denestv_try e (denest_findv e)) => [cc|].
  case=> E'; apply: (denestv_try_sound (oc := denest_findv e)).
  by rewrite E E'.
exact: denestv_try_sound.
Qed.

(* the user version: proot 2 e is the candidate under the conditions *)
Theorem denestv_eq env e c cs : denestv e = Some (c, cs) ->
  all_conds r env cs -> proot r 2 (rinterp r env e) = rinterp r env c.
Proof. by move=> H /all_condsP; exact: denestv_sound H. Qed.

Lemma denest_rootc_sound env n t : holds r env (denest_rootc n t).2 ->
  rinterp r env (denest_rootc n t).1 = rinterp r env (RRootE n t).
Proof.
rewrite /denest_rootc; case: (Pos.eqb_spec n 2) => [->|//].
case E : (denest1 t) => [c|]; first by move=> _; exact: denest1_sound.
by case E2 : (denestv t) => [[c cs]|] // H; exact/esym/(denestv_sound E2).
Qed.

Theorem denest_rwc_sound env e : holds r env (denest_rwc e).2 ->
  rinterp r env (denest_rwc e).1 = rinterp r env e.
Proof.
elim: e => //= [n a IH|a IHa b IHb|a IH|a IHa b IHb|a IHa b IHb|a IH k|a IH].
- case E : (denest_rwc a) IH => [a' c1] IH.
  case E2 : (denest_rootc n a') => [b c2] /holds_cat [H1 H2] /=.
  have := @denest_rootc_sound env n a'; rewrite E2 /= => -> //.
  by rewrite /= IH.
- case Ea : (denest_rwc a) IHa => [a' c1] IHa.
  case Eb : (denest_rwc b) IHb => [b' c2] IHb /holds_cat [H1 H2] /=.
  by rewrite IHa ?IHb.
- by case Ea : (denest_rwc a) IH => [a' c1] IH /= /IH ->.
- case Ea : (denest_rwc a) IHa => [a' c1] IHa.
  case Eb : (denest_rwc b) IHb => [b' c2] IHb /holds_cat [H1 H2] /=.
  by rewrite IHa ?IHb.
- case Ea : (denest_rwc a) IHa => [a' c1] IHa.
  case Eb : (denest_rwc b) IHb => [b' c2] IHb /holds_cat [H1 H2] /=.
  by rewrite IHa ?IHb.
- by case Ea : (denest_rwc a) IH => [a' c1] IH /= /IH ->.
by case Ea : (denest_rwc a) IH => [a' c1] IH /= /IH ->.
Qed.

Theorem radcan_eq_denest env e1 e2 cs :
  radcan_check_denest e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_denest.
have := @denest_rwc_sound env e1; case: (denest_rwc e1) => [e1' c1] /= S1.
have := @denest_rwc_sound env e2; case: (denest_rwc e2) => [e2' c2] /= S2.
case E : (radcan_check e1' e2') => [cs'|] // -[<-].
move=> /all_condsP /holds_dedup /holds_cat [/S1 <- /holds_cat [/S2 <- H]].
exact: radcan_eq_cond E (holds_all_conds H).
Qed.

End DenestSound.

(* refined conditions (Refine.v), as used by the tactics *)

Theorem radcan_eq_denest_refined (F : numFieldType) (r : posroot F) env
    e1 e2 cs rcs :
  radcan_check_denest e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_denest H); apply: all_conds_bridge_back.
by apply: refine_sound; rewrite Hr.
Qed.

Theorem denestv_eq_refined (F : numFieldType) (r : posroot F) env e c cs rcs :
  denestv e = Some (c, cs) -> refine cs = rcs ->
  all_rconds F (proot r) env rcs ->
  proot r 2 (rinterp r env e) = rinterp r env c.
Proof.
move=> H Hr Hc; apply: (denestv_eq H); apply: all_conds_bridge_back.
by apply: refine_sound; rewrite Hr.
Qed.
