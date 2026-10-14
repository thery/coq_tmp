(* Reified syntax of unnested radical expressions (milestone M1) and its     *)
(* interpretation in a numFieldType equipped with a posroot.                 *)
(*                                                                            *)
(*   rexpr        == syntax: integer constants, variables, + - *, inverse,    *)
(*                   powers and                                               *)
(*                   radicals [RRoot n p] = proot n p, n, p : positive        *)
(*                   and [RRootE n e] = proot n e (e any expression, M3)      *)
(*   pos2F p      == the positive p seen in F, i.e. (Pos.to_nat p)%:R        *)
(*   Z2F z        == the integer z seen in F                                  *)
(*   rinterp_gen rt env e == value of e in F, roots taken with rt           *)
(*   rinterp r env e == rinterp_gen (proot r) env e, r : posroot F           *)
(*   rinterp0 env e  == rinterp_gen (fun _ _ => 0) env e (root-free e)       *)
(*   no_root e       == e contains no RRoot / RRootE                         *)
(*                   variable RVar i read as  nth 0 env i  (env : seq F)      *)
(*                                                                            *)
(* Root indices and radicands are positive, so every RRoot is well formed     *)
(* (0 < n, 0 < p): soundness never needs a well-formedness side condition.    *)
(* For RRootE the radicand may be negative: the normaliser records the side   *)
(* conditions it needs (see Radcan.v).                                        *)
(* Numerals of F are  k%:R  with k : nat; the reification tactic turns k      *)
(* into  RCst (Z.of_nat k)  and  rinterp  gives back  (Pos.to_nat _)%:R  which *)
(* is convertible to k%:R.                                                    *)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Inductive rexpr : Type :=
  | RCst  : Z -> rexpr                  (* integer constant              *)
  | RVar  : nat -> rexpr                (* RVar i = nth 0 env i          *)
  | RRoot : positive -> positive -> rexpr (* RRoot n p = proot n p       *)
  | RRootE : positive -> rexpr -> rexpr (* RRootE n e = proot n e        *)
  | RAdd  : rexpr -> rexpr -> rexpr
  | ROpp  : rexpr -> rexpr
  | RSub  : rexpr -> rexpr -> rexpr
  | RMul  : rexpr -> rexpr -> rexpr
  | RPow  : rexpr -> nat -> rexpr       (* e ^+ k                        *)
  | RInv  : rexpr -> rexpr.             (* e ^-1  (a / b is a * b^-1)    *)

Section Interp.

Variable F : numFieldType.

Definition pos2F (p : positive) : F := (Pos.to_nat p)%:R.

Definition Z2F (z : Z) : F :=
  match z with
  | Z0 => 0
  | Zpos p => pos2F p
  | Zneg p => - pos2F p
  end.

(* interpretation with an arbitrary root function rt *)
Variable rt : nat -> F -> F.
Variable env : seq F.

Fixpoint rinterp_gen (e : rexpr) : F :=
  match e with
  | RCst z => Z2F z
  | RVar i => nth 0 env i
  | RRoot n p => rt (Pos.to_nat n) (pos2F p)
  | RRootE n e1 => rt (Pos.to_nat n) (rinterp_gen e1)
  | RAdd e1 e2 => rinterp_gen e1 + rinterp_gen e2
  | ROpp e1 => - rinterp_gen e1
  | RSub e1 e2 => rinterp_gen e1 - rinterp_gen e2
  | RMul e1 e2 => rinterp_gen e1 * rinterp_gen e2
  | RPow e1 k => rinterp_gen e1 ^+ k
  | RInv e1 => (rinterp_gen e1)^-1
  end.

End Interp.

(* the interpretation with the roots of r : posroot F *)
Notation rinterp r := (rinterp_gen (proot r)).

(* the interpretation without roots (no posroot needed): meaningful for     *)
(* root-free expressions, where it is the user's term                       *)
Notation rinterp0 := (rinterp_gen (fun _ _ => 0)).

Fixpoint no_root (e : rexpr) : bool :=
  match e with
  | RCst _ | RVar _ => true
  | RRoot _ _ | RRootE _ _ => false
  | RAdd e1 e2 | RSub e1 e2 | RMul e1 e2 => no_root e1 && no_root e2
  | ROpp e1 | RPow e1 _ | RInv e1 => no_root e1
  end.

Lemma rinterp_no_root (F : numFieldType) (rt1 rt2 : nat -> F -> F) env e :
  no_root e -> rinterp_gen rt1 env e = rinterp_gen rt2 env e.
Proof.
elim: e => //= [e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 k|e1 IH1].
- by case/andP => /IH1 -> /IH2 ->.
- by move/IH1 ->.
- by case/andP => /IH1 -> /IH2 ->.
- by case/andP => /IH1 -> /IH2 ->.
- by move/IH1 ->.
by move/IH1 ->.
Qed.

(* ------------------------------------------------------------------------ *)
(* Side conditions recorded by the normaliser (Radcan.v)                    *)
(*   CGe0 e   == 0 <= e          CNeq0 e  == e != 0                          *)
(*   cond_interp_gen rt env c / all_conds_gen rt env cs == their meaning     *)
(*     (all_conds_gen: a plain conjunction once cs is concrete)              *)
(*   cond_interp r env c / all_conds r env cs == the same with proot r       *)
(*   all_conds0 env cs == the same without roots                             *)
(* ------------------------------------------------------------------------ *)

Inductive cond : Type :=
  | CGe0 : rexpr -> cond     (* 0 <= e *)
  | CNeq0 : rexpr -> cond.   (* e != 0 *)

Section CondInterpGen.

Variable F : numFieldType.
Variable rt : nat -> F -> F.
Variable env : seq F.

Definition cond_interp_gen (c : cond) : Prop :=
  match c with
  | CGe0 e => 0 <= rinterp_gen rt env e
  | CNeq0 e => rinterp_gen rt env e != 0
  end.

Fixpoint all_conds_gen (cs : seq cond) : Prop :=
  match cs with
  | [::] => True
  | c :: cs' => if cs' is [::] then cond_interp_gen c
                else cond_interp_gen c /\ all_conds_gen cs'
  end.

End CondInterpGen.

Section CondInterp.

Variable F : numFieldType.
Variable r : posroot F.
Variable env : seq F.

Definition cond_interp (c : cond) : Prop :=
  match c with
  | CGe0 e => 0 <= rinterp r env e
  | CNeq0 e => rinterp r env e != 0
  end.

Fixpoint all_conds (cs : seq cond) : Prop :=
  match cs with
  | [::] => True
  | c :: cs' => if cs' is [::] then cond_interp c else cond_interp c /\ all_conds cs'
  end.

End CondInterp.

(* conditions in the root-free case *)
Notation all_conds0 := (all_conds_gen (fun _ _ => 0)).

Lemma all_conds_bridge (F : numFieldType) (r : posroot F) env cs :
  all_conds r env cs -> all_conds_gen (proot r) env cs.
Proof. by elim: cs => [|c cs IH] //=. Qed.
