(******************************************************************************)
(* SymTac: the tactic radcan_sym for roots given by hypotheses (Sym.v, M15).  *)
(*   radcan_sym == proves a = b using the hypotheses h : y ^+ n = B and      *)
(*                 h : y = B of the context (y an atom, n a literal > 0, B    *)
(*                 any expression of the field of the goal) as rewriting      *)
(*                 rules y ^+ n -> B (y -> B);                                *)
(*                 the result holds for every y satisfying them.  The         *)
(*                 cancellation conditions (B != 0), if any, are left as      *)
(*                 goals.  Roots proot r n a of the goal are opaque atoms.    *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan Tactic Sym.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* (rels, hs, env'): the relations y ^+ n = B and y = B (n = 1) of the
   context, y an atom of the field T, with their proofs
   hs = (h1, (h2, ... tt)) in the order of rels *)
Ltac radcan_sym_collect T env rels hs :=
  match goal with
  | h : ?y ^+ ?n = ?B |- _ =>
      lazymatch hs with
      | context [h] => fail
      | _ =>
        let _ := constr:(@erefl T y) in
        lazymatch radcan_poslit n with
        | true =>
          let p := radcan_reify_term tt y env in
          lazymatch p with
          | (RVar ?i, ?env1) =>
            let q := radcan_reify_term tt B env1 in
            lazymatch q with (?eB, ?env2) =>
              let n := eval vm_compute in n in
              radcan_sym_collect T env2 ((i, n, eB) :: rels) (h, hs)
            end
          end
        end
      end
  | h : ?y = ?B |- _ =>
      lazymatch hs with
      | context [h] => fail
      | _ =>
        let _ := constr:(@erefl T y) in
        let p := radcan_reify_term tt y env in
        lazymatch p with
        | (RVar ?i, ?env1) =>
          let q := radcan_reify_term tt B env1 in
          lazymatch q with (?eB, ?env2) =>
            radcan_sym_collect T env2 ((i, 1%N, eB) :: rels) (h, hs)
          end
        end
      end
  | _ => constr:((rels, hs, env))
  end.

(* proves rels_hold from the hypotheses hs *)
Ltac radcan_sym_close hs :=
  lazymatch hs with
  | tt => exact: I
  | (?h, tt) => exact: h
  | (?h, ?hs1) => split; [exact: h | radcan_sym_close hs1]
  end.

Ltac radcan_sym_with rt :=
  lazymatch goal with
  | |- @eq ?T ?a ?b =>
    let p := radcan_reify_term tt a (@nil T) in
    lazymatch p with (?ea, ?env1) =>
    let q := radcan_reify_term tt b env1 in
    lazymatch q with (?eb, ?env2) =>
    let c := radcan_sym_collect T env2 (@nil srel) tt in
    lazymatch c with (?rels, ?hs, ?env) =>
      change (rinterp_gen rt env ea = rinterp_gen rt env eb);
      let k := eval vm_compute in (radcan_check_sym rels ea eb) in
      lazymatch k with
      | Some ?cs =>
        apply: (@radcan_eq_cond_sym _ rt env rels ea eb cs);
        [vm_compute; reflexivity
        | cbv beta iota delta [rels_hold]; radcan_sym_close hs
        | radcan_split_conds]
      | None => fail "radcan_sym: the normal forms differ"
      end
    end end end
  end.

Ltac radcan_sym :=
  lazymatch goal with
  | |- context [proot ?r _ _] => radcan_sym_with (proot r)
  | |- @eq ?T _ _ => radcan_sym_with (fun (_ : nat) (_ : T) => 0 : T)
  end.
