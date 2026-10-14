(******************************************************************************)
(* Tactic: reification into rexpr (Syntax.v) and the radcan tactics.          *)
(*   radcan_reify r == changes a = b into rinterp r env ea = rinterp r env eb *)
(*      recognised: + - * ^-1 (so /) ^+ k, 0 1 k%:R, and the roots            *)
(*      proot r n a, n.-root a (rootC_posroot), rootR n a (rootR_posroot)     *)
(*      with a numeral index n > 0 (RRoot n p for a numeral radicand p > 0,   *)
(*      RRootE n e otherwise); any other subterm is an atom RVar i, env lists *)
(*      the atoms (syntactically distinct terms are distinct atoms)           *)
(*   radcan        == proves a = b when both sides have the same normal form, *)
(*                    leaving the side conditions refined by Refine.v         *)
(*                    (e.g. 1 < x); uses the oddroot / negroot available      *)
(*   radcan_raw    == the same with the raw conditions (0 <= B, B != 0)       *)
(*   radcan_with r == radcan with an explicit root structure r                *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC RootR Syntax Radcan Refine OddRoot.
From Radcan Require Import NegRootC.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* conversion unfolds Z2F first and pos2F last (never natmul first): a big
   numeral (Pos.to_nat p)%:R is never expanded in unary *)
Strategy expand [Z2F].
Strategy 1000 [pos2F].

(* true iff p is a closed positive literal (binary, never expanded) *)
Ltac radcan_plit p :=
  lazymatch p with
  | xH => constr:(true)
  | xO ?q => radcan_plit q
  | xI ?q => radcan_plit q
  | _ => constr:(false)
  end.

(* true iff k is a nat literal, after evaluation (k may be Pos.to_nat p) *)
Ltac radcan_lit_aux k :=
  lazymatch k with
  | O => constr:(true)
  | S ?k => radcan_lit_aux k
  | _ => constr:(false)
  end.
Ltac radcan_lit k := let k := eval vm_compute in k in radcan_lit_aux k.

(* true iff k is a nat literal > 0, after evaluation *)
Ltac radcan_poslit k :=
  let k := eval vm_compute in k in
  lazymatch k with
  | O => constr:(false)
  | _ => radcan_lit_aux k
  end.

(* true iff a is 1 or k%:R with k a nat literal > 0 *)
Ltac radcan_radlit a :=
  lazymatch a with
  | 1 => constr:(true)
  | (Pos.to_nat ?p)%:R => radcan_plit p
  | pos2F _ ?p => radcan_plit p
  | (?k)%:R => radcan_poslit k
  | _ => constr:(false)
  end.

(* a nat literal k > 0 as a positive literal *)
Ltac radcan_pos k := let p := eval vm_compute in (Pos.of_nat k) in constr:(p).

(* a radicand recognised by radcan_radlit as a positive literal *)
Ltac radcan_radicand a :=
  lazymatch a with
  | 1 => constr:(1%positive)
  | (Pos.to_nat ?p)%:R => constr:(p)
  | pos2F _ ?p => constr:(p)
  | (?k)%:R => radcan_pos k
  end.

(* (i, env'): index of the atom x in env, added at the end if absent *)
Ltac radcan_atom x env n :=
  lazymatch env with
  | nil => constr:((n, x :: nil))
  | x :: _ => constr:((n, env))
  | ?y :: ?env1 =>
      let p := radcan_atom x env1 (S n) in
      lazymatch p with (?i, ?env2) => constr:((i, y :: env2)) end
  end.

(* reify t with atoms env: returns (e, env') *)
Ltac radcan_reify_term r t env :=
  let rec go t env :=
    let bin c a b :=
      let p := go a env in
      lazymatch p with (?x, ?env1) =>
        let q := go b env1 in
        lazymatch q with (?y, ?env2) => constr:((c x y, env2)) end end in
    let atom t :=
      let p := radcan_atom t env O in
      lazymatch p with (?i, ?env1) => constr:((RVar i, env1)) end in
    let root n a t :=
      lazymatch radcan_poslit n with
      | true =>
          lazymatch radcan_radlit a with
          | true =>
              let n := radcan_pos n in let p := radcan_radicand a in
              constr:((RRoot n p, env))
          | false =>
              let n := radcan_pos n in
              let p := go a env in
              lazymatch p with (?x, ?env1) => constr:((RRootE n x, env1)) end
          end
      | false => atom t
      end in
    lazymatch t with
    | ?a + ?b => bin RAdd a b
    | - ?a =>
        let p := go a env in
        lazymatch p with (?x, ?env1) => constr:((ROpp x, env1)) end
    | ?a * ?b => bin RMul a b
    | (?a)^-1 =>
        let p := go a env in
        lazymatch p with (?x, ?env1) => constr:((RInv x, env1)) end
    | ?a ^+ ?k =>
        lazymatch radcan_lit k with
        | true =>
            let p := go a env in
            lazymatch p with (?x, ?env1) =>
              let k := eval vm_compute in k in constr:((RPow x k, env1))
            end
        | false => atom t
        end
    | proot _ ?n ?a =>
        root n a t
    | ?n.-root ?a =>
        root n a t
    | rootR ?n ?a =>
        root n a t
    | 0 => constr:((RCst Z0, env))
    | 1 => constr:((RCst (Zpos 1), env))
    | pos2F _ ?p =>
        lazymatch radcan_plit p with
        | true => constr:((RCst (Zpos p), env))
        | false => atom t
        end
    | (Pos.to_nat ?p)%:R =>
        lazymatch radcan_plit p with
        | true => constr:((RCst (Zpos p), env))
        | false => atom t
        end
    | (?k)%:R =>
        lazymatch radcan_lit k with
        | true =>
            let z := eval vm_compute in (Z.of_nat k) in constr:((RCst z, env))
        | false => atom t
        end
    | _ => atom t
    end in
  go t env.

Ltac radcan_reify r :=
  lazymatch goal with
  | |- @eq ?T ?a ?b =>
      let p := radcan_reify_term r a (@nil T) in
      lazymatch p with (?ea, ?env1) =>
        let q := radcan_reify_term r b env1 in
        lazymatch q with (?eb, ?env) =>
          change (rinterp r env ea = rinterp r env eb)
        end
      end
  end.

(* the root structure, read from the roots occurring in the goal *)
Ltac radcan_find_root :=
  lazymatch goal with
  | |- context [proot ?r _ _] => constr:(r)
  | |- context [@nthroot ?C _ _] => constr:(rootC_posroot C)
  | |- context [@rootR ?R _ _] => constr:(rootR_posroot R)
  | _ => fail "radcan: no root in the goal"
  end.

(* small numerals (Pos.to_nat p)%:R shown as nat literals *)
Ltac radcan_numerals :=
  rewrite ?/pos2F;
  repeat match goal with
  | |- context [Pos.to_nat ?p] =>
      lazymatch eval vm_compute in (Pos.leb p 1000) with
      | true =>
          let n := eval vm_compute in (Pos.to_nat p) in
          change (Pos.to_nat p) with n
      end
  end.

(* split the side conditions into separate goals, closing the trivial ones *)
Ltac radcan_split_conds :=
  rewrite ?/all_conds ?/cond_interp ?/all_conds_gen ?/cond_interp_gen /=;
  repeat match goal with |- _ /\ _ => split end;
  try exact: I;
  radcan_numerals.

(* refined conditions: Refine.v, reduced by /= to e.g. 1 < x *)
Ltac radcan_split_rconds :=
  rewrite /=;
  repeat match goal with |- _ /\ _ => split end;
  try exact: I;
  radcan_numerals.

(* refined: refined (Refine.v) or raw conditions; o: tt (generic checker),
   o : oddroot r (odd mode) or o : negroot r (neg mode) *)
Ltac radcan_with_gen refined r o :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let mode := lazymatch o with
                  | tt => constr:(0%N)
                  | _ => lazymatch type of o with
                         | oddroot _ => constr:(1%N)
                         | negroot _ => constr:(2%N)
                         end
                  end in
      let c := lazymatch mode with
               | 0%N => eval vm_compute in (radcan_check e1 e2)
               | 1%N => eval vm_compute in (radcan_check_odd e1 e2)
               | 2%N => eval vm_compute in (radcan_check_neg e1 e2)
               end in
      lazymatch c with
      | Some ?cs =>
          lazymatch refined with
          | true =>
              let rcs := eval vm_compute in (refine cs) in
              lazymatch mode with
              | 0%N =>
                  apply: (@radcan_eq_refined _ r env e1 e2 cs rcs);
                    [vm_compute; reflexivity | vm_compute; reflexivity
                    | radcan_split_rconds]
              | 1%N =>
                  apply: (@radcan_eq_refined_odd _ r o env e1 e2 cs rcs);
                    [vm_compute; reflexivity | vm_compute; reflexivity
                    | radcan_split_rconds]
              | 2%N =>
                  apply: (@radcan_eq_refined_neg _ r o env e1 e2 cs rcs);
                    [vm_compute; reflexivity | vm_compute; reflexivity
                    | radcan_split_rconds]
              end
          | false =>
              lazymatch mode with
              | 0%N =>
                  apply: (@radcan_eq_cond _ r env e1 e2 cs);
                    [vm_compute; reflexivity | radcan_split_conds]
              | 1%N =>
                  apply: (@radcan_eq_cond_odd _ r o env e1 e2 cs);
                    [vm_compute; reflexivity | radcan_split_conds]
              | 2%N =>
                  apply: (@radcan_eq_cond_neg _ r o env e1 e2 cs);
                    [vm_compute; reflexivity | radcan_split_conds]
              end
          end
      | None => fail "radcan: the normal forms differ"
      end
  end.

(* goals without roots: no root structure is needed *)
Ltac radcan0_gen refined :=
  lazymatch goal with
  | |- @eq ?T ?a ?b =>
      let p := radcan_reify_term tt a (@nil T) in
      lazymatch p with (?ea, ?env1) =>
        let q := radcan_reify_term tt b env1 in
        lazymatch q with (?eb, ?env) =>
          change (rinterp0 env ea = rinterp0 env eb);
          let c := eval vm_compute in (radcan_check ea eb) in
          lazymatch c with
          | Some ?cs =>
              lazymatch refined with
              | true =>
                  let rcs := eval vm_compute in (refine cs) in
                  apply: (@radcan_eq_refined0 _ env ea eb cs rcs erefl erefl);
                    [vm_compute; reflexivity | vm_compute; reflexivity
                    | radcan_split_rconds]
              | false =>
                  apply: (@radcan_eq_cond0 _ env ea eb cs erefl erefl);
                    [vm_compute; reflexivity | radcan_split_conds]
              end
          | None => fail "radcan: the normal forms differ"
          end
        end
      end
  end.

Ltac radcan_gen refined :=
  lazymatch goal with
  | |- context [proot ?r _ _] =>
      lazymatch goal with
      | o : oddroot r |- _ => radcan_with_gen refined r o
      | w : negroot r |- _ => radcan_with_gen refined r w
      | _ => radcan_with_gen refined r tt
      end
  | |- context [@nthroot ?C _ _] =>
      radcan_with_gen refined (rootC_posroot C) (rootC_negroot C)
  | |- context [@rootR ?R _ _] =>
      radcan_with_gen refined (rootR_posroot R) (rootR_oddroot R)
  | _ => radcan0_gen refined
  end.

Ltac radcan_with r := radcan_with_gen true r tt.
Ltac radcan := radcan_gen true.
Ltac radcan_raw := radcan_gen false.
