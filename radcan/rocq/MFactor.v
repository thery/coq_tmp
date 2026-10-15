(******************************************************************************)
(* MFactor: factorisation of multivariate integer polynomials (homogeneous    *)
(* polynomials and factors linear in one variable).  Nothing here is          *)
(* verified: callers check every result by multiplication.                    *)
(* A polynomial is a list of (coefficient, exponent vector) sorted by         *)
(* decreasing lex order (variable 0 most significant), no zero coefficient,   *)
(* exponent vectors without trailing zeros.                                   *)
(*   madd, msub, mmul, mscale == arithmetic                                   *)
(*   mdiv f g       == exact quotient f / g, if any                           *)
(*   mprim f        == primitive part, positive leading coefficient           *)
(*   to_uni i f     == f as a dense polynomial in variable i, coefficients    *)
(*                     in the other variables (lowest degree first)           *)
(*   of_uni i cs    == the converse                                           *)
(*   zfactor f      == irreducible factors with repetitions of a univariate   *)
(*                     f (square-free decomposition + ufactor)                *)
(*   mfactor f      == factors of f (f <> 0) with repetitions, product =      *)
(*                     mprim f: monomial content, univariate case,            *)
(*                     homogeneous case (dehomogenise, recurse,               *)
(*                     rehomogenise), factors of degree 0 or 1 in some        *)
(*                     variable (divisors of the leading and constant         *)
(*                     coefficients); other factors are returned unsplit      *)
(*   mfact_with st3 == the same loop with st3 as a fallback (MFactorEEZ)      *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith.
From mathcomp Require Import all_boot.
From Radcan Require Import IrrFactor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* run step at most 2 ^ k times, stopping at the first done state *)
Fixpoint iterd (T : Type) (done : T -> bool) (step : T -> T) (k : nat)
  (s : T) : T :=
  if done s then s else
  match k with
  | O => step s
  | S k' => iterd done step k' (iterd done step k' s)
  end.

(* Monomials *)

Definition mono := seq nat.
Definition mpoly := seq (Z * mono).

Fixpoint drop0n (l : seq nat) : seq nat :=
  if l is 0%N :: l' then drop0n l' else l.

Definition etrim (e : mono) : mono := rev (drop0n (rev e)).

Fixpoint eadd (a b : mono) : mono :=
  match a, b with
  | [::], _ => b
  | _, [::] => a
  | x :: a', y :: b' => (x + y)%N :: eadd a' b'
  end.

Definition allz (e : mono) : bool := all (fun x => x == 0%N) e.

Fixpoint ecmp (a b : mono) {struct a} : comparison :=
  match a with
  | [::] => if allz b then Eq else Lt
  | x :: a' =>
    match b with
    | [::] => if allz a then Eq else Gt
    | y :: b' =>
      if (x < y)%N then Lt else if (y < x)%N then Gt else ecmp a' b'
    end
  end.

Fixpoint ele (a b : mono) {struct a} : bool :=
  match a, b with
  | [::], _ => true
  | _, [::] => allz a
  | x :: a', y :: b' => (x <= y)%N && ele a' b'
  end.

(* b - a, when a <= b *)
Definition ediv (b a : mono) : option mono :=
  if ele a b then
    Some (etrim (mkseq (fun i => (nth 0%N b i - nth 0%N a i)%N) (size b)))
  else None.

Definition emin (a b : mono) : mono :=
  etrim (mkseq (fun i => minn (nth 0%N a i) (nth 0%N b i))
               (minn (size a) (size b))).

Definition eset (e : mono) (i k : nat) : mono := etrim (set_nth 0%N e i k).

(* Polynomials *)

Fixpoint madd (p q : mpoly) {struct p} : mpoly :=
  match p with
  | [::] => q
  | (c, e) :: p' =>
    let fix aux q :=
      match q with
      | [::] => p
      | (d, f) :: q' =>
        match ecmp e f with
        | Gt => (c, e) :: madd p' q
        | Lt => (d, f) :: aux q'
        | Eq => if Z.eqb (c + d) 0 then madd p' q' else (c + d, e) :: madd p' q'
        end
      end in aux q
  end.

Definition mopp (p : mpoly) : mpoly := map (fun t => (- t.1, t.2)) p.
Definition msub (p q : mpoly) : mpoly := madd p (mopp q).

Definition mscale (c : Z) (p : mpoly) : mpoly :=
  if Z.eqb c 0 then [::] else map (fun t => (c * t.1, t.2)) p.

Definition mmul_term (t : Z * mono) (q : mpoly) : mpoly :=
  map (fun s => (t.1 * s.1, eadd t.2 s.2)) q.

Definition mmul (p q : mpoly) : mpoly :=
  foldr (fun t acc => madd (mmul_term t q) acc) [::] p.

Definition mconst (c : Z) : mpoly := if Z.eqb c 0 then [::] else [:: (c, [::])].
Definition mone : mpoly := [:: (1, [::])].
Definition mvar (i : nat) : mpoly := [:: (1, eset [::] i 1)].

Fixpoint mpow (p : mpoly) (n : nat) : mpoly :=
  if n is S n' then mmul p (mpow p n') else mone.

(* sort an arbitrary list of terms *)
Definition mnorm (l : seq (Z * mono)) : mpoly :=
  foldr (fun t acc =>
           if Z.eqb t.1 0 then acc else madd [:: (t.1, etrim t.2)] acc)
    [::] l.

Fixpoint meqb (p q : mpoly) : bool :=
  match p, q with
  | [::], [::] => true
  | (c, e) :: p', (d, f) :: q' => Z.eqb c d && (e == f) && meqb p' q'
  | _, _ => false
  end.

Definition mlc (p : mpoly) : Z := if p is (c, _) :: _ then c else 0.

Definition mcont (p : mpoly) : Z := foldr (fun t g => Z.gcd t.1 g) 0 p.

Definition mprim (p : mpoly) : mpoly :=
  let c := mcont p in
  if Z.eqb c 0 then p else
  let c' := if Z.ltb (mlc p) 0 then - c else c in
  map (fun t => (Z.div t.1 c', t.2)) p.

(* exact division *)

Definition mdiv_step (g : mpoly) (s : option (mpoly * mpoly)) :=
  match s, g with
  | Some (q, (c, e) :: r), (d, h) :: _ =>
    if Z.eqb (Z.modulo c d) 0 then
      if ediv e h is Some u then
        let t := (Z.div c d, u) in
        Some (madd q [:: t], msub ((c, e) :: r) (mmul_term t g))
      else None
    else None
  | Some (_, [::]), _ => s
  | _, _ => None
  end.

Definition mdiv_done (s : option (mpoly * mpoly)) : bool :=
  if s is Some (_, r) then nilp r else true.

Definition mdiv_fuel := 40%N.

Definition mdiv (f g : mpoly) : option mpoly :=
  if g is [::] then None else
  if iterd mdiv_done (mdiv_step g) mdiv_fuel (Some ([::], f))
    is Some (q, [::]) then Some q else None.

(* variables, degrees *)

Definition mvars (p : mpoly) : seq nat :=
  let n := foldr (fun t m => maxn (size t.2) m) 0%N p in
  filter (fun i => has (fun t => (0 < nth 0%N t.2 i)%N) p) (iota 0 n).

Definition mdeg (i : nat) (p : mpoly) : nat :=
  foldr (fun t m => maxn (nth 0%N t.2 i) m) 0%N p.

Definition mtdeg (p : mpoly) : nat :=
  foldr (fun t m => maxn (sumn t.2) m) 0%N p.

Definition mhomog (p : mpoly) : bool :=
  all (fun t => sumn t.2 == mtdeg p) p.

(* univariate views *)

Definition to_uni (i : nat) (p : mpoly) : seq mpoly :=
  mkseq (fun k => [seq (t.1, eset t.2 i 0) | t <- p & nth 0%N t.2 i == k])
        (mdeg i p).+1.

Definition of_uni (i : nat) (cs : seq mpoly) : mpoly :=
  foldr madd [::]
    (map (fun kc => map (fun t => (t.1, eset t.2 i kc.1)) kc.2)
         (zip (iota 0 (size cs)) cs)).

Definition const_of (p : mpoly) : Z :=
  if p is (c, _) :: _ then c else 0.

Definition zpoly_of (i : nat) (p : mpoly) : zpoly :=
  zn (map const_of (to_uni i p)).

Definition mpoly_of (i : nat) (p : zpoly) : mpoly :=
  of_uni i (map mconst p).

(* Univariate factoring with repetitions *)

Fixpoint zprem_loop (fuel : nat) (g r : zpoly) : zpoly :=
  match fuel with
  | O => r
  | S f =>
    if (size r < size g)%N then r else
    zprem_loop f g (zsub (zscale (zlc g) r)
                         (zmul (zshift (size r - size g) [:: zlc r]) g))
  end.

Fixpoint zgcd_loop (fuel : nat) (a b : zpoly) : zpoly :=
  match fuel with
  | O => a
  | S f =>
    if b is [::] then a else
    zgcd_loop f b (zprim (zprem_loop (size a).+1 b a))
  end.

Definition zgcd (a b : zpoly) : zpoly :=
  zprim (zgcd_loop (size a + size b).+1 (zprim a) (zprim b)).

Fixpoint zmult (fuel : nat) (p f : zpoly) : seq zpoly :=
  match fuel with
  | O => [::]
  | S fu => if zdivZ f p is Some q then p :: zmult fu p q else [::]
  end.

Definition zfactor (f0 : zpoly) : seq zpoly :=
  let f := zprim (zn f0) in
  if (size f <= 2)%N then (if size f == 2%N then [:: f] else [::]) else
  let g := zgcd f (zderiv f) in
  let s := if (size g <= 1)%N then f else
           if zdivZ f g is Some s then s else f in
  flatten (map (fun p => zmult (size f) p f) (ufactor s)).

(* Integer primes by trial division *)

Definition zp_step (s : Z * Z * seq Z) : Z * Z * seq Z :=
  let: (n, d, acc) := s in
  if Z.ltb n (d * d) then (1, d, n :: acc) else
  if Z.eqb (Z.modulo n d) 0 then (Z.div n d, d, d :: acc) else (n, d + 1, acc).

Definition zprimes (n : Z) : seq Z :=
  let: (_, _, acc) :=
    iterd (fun s => Z.leb s.1.1 1) zp_step 40 (Z.abs n, 2, [::]) in acc.

(* Divisors of a product of factors *)

Fixpoint mgroup (l : seq mpoly) : seq (mpoly * nat) :=
  if l is p :: l' then
    let g := mgroup l' in
    if has (fun pm => meqb pm.1 p) g then
      map (fun pm => if meqb pm.1 p then (pm.1, pm.2.+1) else pm) g
    else (p, 1%N) :: g
  else [::].

Definition mdivisors (l : seq mpoly) : seq mpoly :=
  foldr (fun pm ds =>
           flatten (map (fun j => map (mmul (mpow pm.1 j)) ds)
                        (iota 0 pm.2.+1)))
        [:: mone] (mgroup l).

(* value at x_i = 2 i + 3, a cheap divisibility filter *)
Definition meval (p : mpoly) : Z :=
  foldr (fun t v =>
    t.1 * foldr Z.mul 1
            (map (fun ik => Z.of_nat (2 * ik.1 + 3) ^ Z.of_nat ik.2)
                 (zip (iota 0 (size t.2)) t.2)) + v) 0 p.

Fixpoint find_div_aux (f : mpoly) (fv : Z) (gs : seq mpoly) :=
  if gs is g :: gs' then
    let gv := meval g in
    if Z.eqb gv 0 || Z.eqb (Z.modulo fv gv) 0 then
      if mdiv f g is Some q then Some (g, q) else find_div_aux f fv gs'
    else find_div_aux f fv gs'
  else None.

Definition find_div (f : mpoly) (gs : seq mpoly) : option (mpoly * mpoly) :=
  find_div_aux f (meval f) gs.

(* Monomial content *)

Definition mmono_cont (p : mpoly) : mono :=
  if p is t :: p' then foldr (fun s e => emin s.2 e) t.2 p' else [::].

Definition mvar_factors (e : mono) : seq mpoly :=
  flatten (map (fun ik => nseq ik.2 (mvar ik.1)) (zip (iota 0 (size e)) e)).

(* Homogeneous case *)

Definition dehom (v : nat) (p : mpoly) : mpoly :=
  mnorm (map (fun t => (t.1, eset t.2 v 0)) p).

Definition rehom (v : nat) (p : mpoly) : mpoly :=
  let d := mtdeg p in
  mnorm (map (fun t => (t.1, eset t.2 v (nth 0%N t.2 v + (d - sumn t.2)))) p).

(* Linear factors in variable x *)

Inductive lres := LFound of mpoly & mpoly | LIrr | LNone.

Definition linear_in (rec : mpoly -> seq mpoly) (x : nat) (f : mpoly) :=
  let cs := to_uni x f in
  let lc := last [::] cs in
  let c0 := head [::] cs in
  let flc := rec lc in
  let polys := filter (fun p => (0 < size (mvars p))%N) flc in
  if find_div f polys is Some (g, q) then LFound g q else
  if (size cs <= 2)%N then LIrr else
  let la := flc ++ map mconst (zprimes (mcont lc)) in
  let lb := rec c0 ++ map mconst (zprimes (mcont c0)) in
  let bs := mdivisors lb in
  let cands :=
    flatten (map (fun a => flatten (map (fun b =>
      [:: of_uni x [:: b; a]; of_uni x [:: mopp b; a]]) bs))
      (mdivisors la)) in
  if find_div f cands is Some (g, q) then LFound g q else LNone.

Fixpoint try_vars (rec : mpoly -> seq mpoly) (f : mpoly) (vs : seq nat) :=
  if vs is x :: vs' then
    match linear_in rec x f with
    | LNone => try_vars rec f vs'
    | r => r
    end
  else LNone.

(* Main loop; st3 rec f is the fallback for an f with no factor of degree *)
(* <= 1 in any variable (rec factors polynomials with fewer variables)   *)

Definition stage3 := (mpoly -> seq mpoly) -> mpoly -> seq mpoly.

Fixpoint mfact_with (st3 : stage3) (fuel : nat) (f0 : mpoly) : seq mpoly :=
  match fuel with
  | O => [:: mprim f0]
  | S fu =>
    let f := mprim f0 in
    let e := mmono_cont f in
    let f1 := map (fun t => (t.1, if ediv t.2 e is Some u then u else t.2)) f in
    let vs := mvars f1 in
    mvar_factors e ++
    match vs with
    | [::] => [::]
    | [:: i] => map (mpoly_of i) (zfactor (zpoly_of i f1))
    | v :: _ =>
      if mhomog f1 then
        map (fun p => mprim (rehom v p)) (mfact_with st3 fu (dehom v f1))
      else
        match try_vars (mfact_with st3 fu) f1 vs with
        | LFound g q => mprim g :: mfact_with st3 fu q
        | LNone => st3 (mfact_with st3 fu) f1
        | LIrr => [:: f1]
        end
    end
  end.

Definition mfact := mfact_with (fun _ f => [:: f]).

Definition mfuel (f : mpoly) : nat := ((mtdeg f).+1 * (size (mvars f)).+1).+1.

Definition mfactor (f : mpoly) : seq mpoly :=
  if f is [::] then [:: f] else mfact (mfuel f) f.

(* product of a list of factors, for checking *)
Definition mprod (l : seq mpoly) : mpoly := foldr mmul mone l.

Definition mcheck (f : mpoly) : bool := meqb (mprod (mfactor f)) (mprim f).

(* Tests: x = variable 0, y = variable 1, z = variable 2, w = variable 3. *)
(* Timings (vm_compute, Rocq 9.1.1) in comments.                         *)

Definition X := mvar 0.
Definition Y := mvar 1.
Definition Z' := mvar 2.
Definition W := mvar 3.
Definition K c := mconst c.

(* Stage 1: homogeneous polynomials *)

(* x^2 - y^2 = (x - y)(x + y), 0.006s *)
Example h1 : mfactor (msub (mpow X 2) (mpow Y 2)) =
  [:: [:: (1, [:: 1%N]); (-1, [:: 0%N; 1%N])];
      [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* x^3 - y^3 = (x - y)(x^2 + x y + y^2), 0.01s *)
Example h2 : mfactor (msub (mpow X 3) (mpow Y 3)) =
  [:: [:: (1, [:: 1%N]); (-1, [:: 0%N; 1%N])];
      [:: (1, [:: 2%N]); (1, [:: 1%N; 1%N]); (1, [:: 0%N; 2%N])]].
Proof. by vm_compute. Qed.

(* x^4 + 4 y^4 = (x^2 - 2 x y + 2 y^2)(x^2 + 2 x y + 2 y^2), 0.008s *)
Example h3 : mfactor (madd (mpow X 4) (mscale 4 (mpow Y 4))) =
  [:: [:: (1, [:: 2%N]); (-2, [:: 1%N; 1%N]); (2, [:: 0%N; 2%N])];
      [:: (1, [:: 2%N]); (2, [:: 1%N; 1%N]); (2, [:: 0%N; 2%N])]].
Proof. by vm_compute. Qed.

(* x^2 + 2 x y + y^2 = (x + y)^2 (not square-free), 0.003s *)
Example h4 : mfactor (mpow (madd X Y) 2) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N])];
      [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* 6 x^2 + x y - 2 y^2 = (3 x + 2 y)(2 x - y), 0.005s *)
Example h5 :
  mfactor (madd (mscale 6 (mpow X 2))
                (msub (mmul X Y) (mscale 2 (mpow Y 2)))) =
  [:: [:: (3, [:: 1%N]); (2, [:: 0%N; 1%N])];
      [:: (2, [:: 1%N]); (-1, [:: 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* x^2 - (y + z)^2 = (x + y + z)(x - y - z), 0.006s *)
Example h6 : mfactor (msub (mpow X 2) (mpow (madd Y Z') 2)) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])];
      [:: (1, [:: 1%N]); (-1, [:: 0%N; 1%N]); (-1, [:: 0%N; 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* x^3 + y^3 + z^3 - 3 x y z, 0.024s *)
Example h7 :
  mfactor (msub (madd (mpow X 3) (madd (mpow Y 3) (mpow Z' 3)))
                (mscale 3 (mmul X (mmul Y Z')))) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])];
      [:: (1, [:: 2%N]); (-1, [:: 1%N; 1%N]); (-1, [:: 1%N; 0%N; 1%N]);
          (1, [:: 0%N; 2%N]); (-1, [:: 0%N; 1%N; 1%N]);
          (1, [:: 0%N; 0%N; 2%N])]].
Proof. by vm_compute. Qed.

(* x^2 (y^4 - z^4): monomial content, then homogeneous, 0.011s *)
Example h8 :
  mcheck (mmul (mpow X 2) (msub (mpow Y 4) (mpow Z' 4))) /\
  size (mfactor (mmul (mpow X 2) (msub (mpow Y 4) (mpow Z' 4)))) = 5%N.
Proof. by vm_compute. Qed.

(* Stage 2: factors of degree <= 1 in some variable *)

(* x y + x + y + 1 = (y + 1)(x + 1), 0.002s *)
Example l1 : mfactor (madd (madd (mmul X Y) X) (madd Y mone)) =
  [:: [:: (1, [:: 0%N; 1%N]); (1, [::])]; [:: (1, [:: 1%N]); (1, [::])]].
Proof. by vm_compute. Qed.

(* x^2 y - y + x^2 - 1 = (y + 1)(x - 1)(x + 1), 0.004s *)
Example l2 :
  mfactor (msub (madd (mmul (mpow X 2) Y) (mpow X 2)) (madd Y mone)) =
  [:: [:: (1, [:: 0%N; 1%N]); (1, [::])]; [:: (1, [:: 1%N]); (-1, [::])];
      [:: (1, [:: 1%N]); (1, [::])]].
Proof. by vm_compute. Qed.

(* x y - 2 x + 3 y - 6 = (y - 2)(x + 3), 0.003s *)
Example l3 :
  mfactor (madd (msub (mmul X Y) (mscale 2 X)) (msub (mscale 3 Y) (K 6))) =
  [:: [:: (1, [:: 0%N; 1%N]); (-2, [::])]; [:: (1, [:: 1%N]); (3, [::])]].
Proof. by vm_compute. Qed.

(* (x^2 + y)(y^2 + x), 0.005s *)
Example l4 : mfactor (mmul (madd (mpow X 2) Y) (madd (mpow Y 2) X)) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 2%N])];
      [:: (1, [:: 2%N]); (1, [:: 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* (x y + z)^2 (x - z), 0.005s *)
Example l5 : mfactor (mmul (mpow (madd (mmul X Y) Z') 2) (msub X Z')) =
  [:: [:: (1, [:: 1%N]); (-1, [:: 0%N; 0%N; 1%N])];
      [:: (1, [:: 1%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])];
      [:: (1, [:: 1%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])]].
Proof. by vm_compute. Qed.

(* (x^2 y + 3 z - 1)(2 x y^2 - z^2 + 5)(x + y + z), 0.11s *)
Example l6 :
  mfactor (mmul (mmul (madd (mmul (mpow X 2) Y) (msub (mscale 3 Z') mone))
                      (madd (mscale 2 (mmul X (mpow Y 2)))
                            (msub (K 5) (mpow Z' 2))))
                (madd X (madd Y Z'))) =
  [:: [:: (1, [:: 1%N]); (1, [:: 0%N; 1%N]); (1, [:: 0%N; 0%N; 1%N])];
      [:: (2, [:: 1%N; 2%N]); (-1, [:: 0%N; 0%N; 2%N]); (5, [::])];
      [:: (1, [:: 2%N; 1%N]); (3, [:: 0%N; 0%N; 1%N]); (-1, [::])]].
Proof. by vm_compute. Qed.

(* (6 x y + 35)(10 x y^2 + 21)(4 x z - 15 y): many divisors, 0.45s *)
Example l7 :
  let f := mmul (mmul (madd (mscale 6 (mmul X Y)) (K 35))
                      (madd (mscale 10 (mmul X (mpow Y 2))) (K 21)))
                (msub (mscale 4 (mmul X Z')) (mscale 15 Y)) in
  mcheck f /\ size (mfactor f) = 3%N.
Proof. by vm_compute. Qed.

(* (x + y + z + 1)^3 (x - 2 y + 3 z), 0.043s *)
Example l8 :
  let f := mmul (mpow (madd X (madd Y (madd Z' mone))) 3)
                (madd (msub X (mscale 2 Y)) (mscale 3 Z')) in
  mcheck f /\ size (mfactor f) = 4%N.
Proof. by vm_compute. Qed.

(* (x w + y z)(x y - z w)(x^2 + y^2 + z^2 + w^2), 0.11s *)
Example l9 :
  let f := mmul (mmul (madd (mmul X W) (mmul Y Z'))
                      (msub (mmul X Y) (mmul Z' W)))
                (madd (mpow X 2) (madd (mpow Y 2)
                                       (madd (mpow Z' 2) (mpow W 2)))) in
  mcheck f /\ size (mfactor f) = 3%N.
Proof. by vm_compute. Qed.

(* Out of reach of stages 1-2 (no factor of degree <= 1 in any variable): *)
(* (210 x^2 + y^3 + 1)(x^2 + 2 y^2 + 11) is returned unsplit, 0.13s      *)
Example f1 :
  let f := mmul (madd (mscale 210 (mpow X 2)) (madd (mpow Y 3) mone))
                (madd (mpow X 2) (madd (mscale 2 (mpow Y 2)) (K 11))) in
  mfactor f = [:: f].
Proof. by vm_compute. Qed.

(* Degenerate inputs: constants, monomials, univariate, sign and content *)
Example d1 :
  [seq mfactor f | f <- [:: K 6; X; mmul (mpow X 2) Y]] =
  [:: [::]; [:: X]; [:: X; X; Y]] /\
  mfactor (mmul (mpow (msub X mone) 2) (madd X (K 2))) =
    [:: msub X mone; msub X mone; madd X (K 2)] /\
  mfactor (mscale (-3) (msub Y (mpow X 2))) = [:: msub (mpow X 2) Y].
Proof. by vm_compute. Qed.
