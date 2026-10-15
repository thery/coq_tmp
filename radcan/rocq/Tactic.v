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
(*                    (e.g. 1 < x); uses the oddroot / negroot available;     *)
(*                    when the plain check fails, the composed pre-pass of    *)
(*                    Prepass.v (fractions, denesting, omega_n with a         *)
(*                    smallroot) runs before the checker                      *)
(*   radcan_raw    == the same with the raw conditions (0 <= B, B != 0)       *)
(*   radcan_with r == radcan with an explicit root structure r                *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC RootR Syntax Radcan Refine OddRoot.
From Radcan Require Import NegRootC RealRoot AbsRoot OmegaRoot OmegaC.
From Radcan Require Import Frac Denest OmegaPass Prepass.
From Radcan Require Import OmegaRoot2 NegCyc CycC Cyclo CycloC.
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

(* closes lhs = v, v the value computed by eval vm_compute of lhs: the
   kernel checks the conversion once, at Qed *)
Ltac radcan_vm_refl :=
  lazymatch goal with |- _ = ?v => vm_cast_no_check (@erefl _ v) end.

(* refined: refined (Refine.v) or raw conditions; o: tt (generic checker),
   o : oddroot r (odd mode), o : negroot r (neg mode), o : realroot r
   (real mode), o : cycroot w (neg mode, omegas merged across indices) or
   o : (cycroot w * cycprim w) (cyclotomic reduction, Cyclo.v) *)
Ltac radcan_with_gen refined r o :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let mode := lazymatch o with
                  | tt => constr:(0%N)
                  | _ => lazymatch type of o with
                         | oddroot _ => constr:(1%N)
                         | negroot _ => constr:(2%N)
                         | realroot _ => constr:(3%N)
                         | cycroot _ => constr:(4%N)
                         | prod (cycroot _) (cycprim _) => constr:(5%N)
                         | prod (cycroot _) (sqrtroot _) => constr:(6%N)
                         end
                  end in
      let c := lazymatch mode with
               | 0%N => eval vm_compute in (radcan_check e1 e2)
               | 1%N => eval vm_compute in (radcan_check_odd e1 e2)
               | 2%N => eval vm_compute in (radcan_check_neg e1 e2)
               | 3%N => eval vm_compute in (radcan_check_real e1 e2)
               | 4%N => eval vm_compute in (radcan_check_negc e1 e2)
               | 5%N => eval vm_compute in (radcan_check_cyc e1 e2)
               | 6%N => eval vm_compute in (radcan_check_negs e1 e2)
               end in
      lazymatch c with
      | Some ?cs =>
          lazymatch refined with
          | true =>
              let rcs := eval vm_compute in (refine cs) in
              lazymatch mode with
              | 0%N =>
                  apply: (@radcan_eq_refined _ r env e1 e2 cs rcs);
                    [radcan_vm_refl | radcan_vm_refl
                    | radcan_split_rconds]
              | 1%N =>
                  apply: (@radcan_eq_refined_odd _ r o env e1 e2 cs rcs);
                    [radcan_vm_refl | radcan_vm_refl
                    | radcan_split_rconds]
              | 2%N =>
                  apply: (@radcan_eq_refined_neg _ r o env e1 e2 cs rcs);
                    [radcan_vm_refl | radcan_vm_refl
                    | radcan_split_rconds]
              | 3%N =>
                  apply: (@radcan_eq_refined_real _ r o env e1 e2 cs rcs);
                    [radcan_vm_refl | radcan_vm_refl
                    | radcan_split_rconds]
              | 4%N =>
                  lazymatch type of o with @cycroot _ _ ?w =>
                  apply: (@radcan_eq_refined_negc _ r w o env e1 e2 cs rcs);
                    [radcan_vm_refl | radcan_vm_refl
                    | radcan_split_rconds]
                  end
              | 5%N =>
                  lazymatch type of o with prod (@cycroot _ _ ?w) _ =>
                  apply: (@radcan_eq_refined_cyc _ r w o.1 o.2 env e1 e2 cs
                            rcs);
                    [radcan_vm_refl | radcan_vm_refl
                    | radcan_split_rconds]
                  end
              | 6%N =>
                  lazymatch type of o with prod (@cycroot _ _ ?w) _ =>
                  apply: (@radcan_eq_refined_negs _ r w o.1 o.2 env e1 e2 cs
                            rcs);
                    [radcan_vm_refl | radcan_vm_refl
                    | radcan_split_rconds]
                  end
              end
          | false =>
              lazymatch mode with
              | 0%N =>
                  apply: (@radcan_eq_cond _ r env e1 e2 cs);
                    [radcan_vm_refl | radcan_split_conds]
              | 1%N =>
                  apply: (@radcan_eq_cond_odd _ r o env e1 e2 cs);
                    [radcan_vm_refl | radcan_split_conds]
              | 2%N =>
                  apply: (@radcan_eq_cond_neg _ r o env e1 e2 cs);
                    [radcan_vm_refl | radcan_split_conds]
              | 3%N =>
                  apply: (@radcan_eq_cond_real _ r o env e1 e2 cs);
                    [radcan_vm_refl | radcan_split_conds]
              | 4%N =>
                  lazymatch type of o with @cycroot _ _ ?w =>
                  apply: (@radcan_eq_cond_negc _ r w o env e1 e2 cs);
                    [radcan_vm_refl | radcan_split_conds]
                  end
              | 5%N =>
                  lazymatch type of o with prod (@cycroot _ _ ?w) _ =>
                  apply: (@radcan_eq_cond_cyc _ r w o.1 o.2 env e1 e2 cs);
                    [radcan_vm_refl | radcan_split_conds]
                  end
              | 6%N =>
                  lazymatch type of o with prod (@cycroot _ _ ?w) _ =>
                  apply: (@radcan_eq_cond_negs _ r w o.1 o.2 env e1 e2 cs);
                    [radcan_vm_refl | radcan_split_conds]
                  end
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
                    [radcan_vm_refl | radcan_vm_refl
                    | radcan_split_rconds]
              | false =>
                  apply: (@radcan_eq_cond0 _ env ea eb cs erefl erefl);
                    [radcan_vm_refl | radcan_split_conds]
              end
          | None => fail "radcan: the normal forms differ"
          end
        end
      end
  end.

Ltac radcan_plain_gen refined :=
  rewrite ?normr_rootR;
  lazymatch goal with
  | |- context [proot ?r _ _] =>
      lazymatch goal with
      | rl : realroot r |- _ =>
          rewrite ?(normr_proot rl); radcan_with_gen refined r rl
      | o : oddroot r |- _ => radcan_with_gen refined r o
      | w : negroot r, cy : @cycroot _ r ?w, cp : @cycprim _ r ?w,
        sq : @sqrtroot _ r ?w |- _ =>
          first [ radcan_with_gen refined r (cy, sq)
                | radcan_with_gen refined r (cy, cp) ]
      | w : negroot r, cy : @cycroot _ r ?w, cp : @cycprim _ r ?w |- _ =>
          radcan_with_gen refined r (cy, cp)
      | w : negroot r, cy : @cycroot _ r ?w, sq : @sqrtroot _ r ?w |- _ =>
          radcan_with_gen refined r (cy, sq)
      | w : negroot r, cy : @cycroot _ r ?w |- _ =>
          radcan_with_gen refined r cy
      | w : negroot r |- _ => radcan_with_gen refined r w
      | _ => radcan_with_gen refined r tt
      end
  | |- context [@nthroot ?C _ _] =>
      first [ radcan_with_gen refined (rootC_posroot C)
                (rootC_cycroot C, rootC_sqrtroot C)
            | radcan_with_gen refined (rootC_posroot C)
                (rootC_cycroot C, rootC_cycprim C) ]
  | |- context [@rootR ?R _ _] =>
      radcan_with_gen refined (rootR_posroot R) (rootR_realroot R)
  | _ => radcan0_gen refined
  end.

(* fallback: the composed pre-pass of Prepass.v (fractions, denesting, and
   omega_rw when ov : smallroot o is given, ov = tt otherwise), iterated at
   most radcan_fuel times, then the checker of the mode *)
Definition radcan_fuel : nat := 4.

(* po: the (root, mode) of a plain check that already failed, or tt; when
   the pre-pass changes neither side and po is (r, o), the same check would
   fail again: fail at once *)
Ltac radcan_pre_with_gen refined r o ov po :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let mode := lazymatch o with
                  | tt => constr:(0%N)
                  | _ => lazymatch type of o with
                         | oddroot _ => constr:(1%N)
                         | negroot _ => constr:(2%N)
                         | realroot _ => constr:(3%N)
                         end
                  end in
      let b := lazymatch mode with 3%N => constr:(true) | _ => constr:(false)
               end in
      let om := lazymatch ov with tt => constr:(false) | _ => constr:(true)
                end in
      let hov := lazymatch mode with
                 | 2%N => lazymatch ov with
                          | tt => constr:(@smallroot_false _ r o)
                          | _ => constr:(fun _ : is_true true => ov)
                          end
                 | _ => constr:(tt)
                 end in
      let p1 := eval vm_compute in (prepass b om radcan_fuel e1) in
      let p2 := eval vm_compute in (prepass b om radcan_fuel e2) in
      lazymatch p1 with (?f1, ?cs1) =>
      lazymatch p2 with (?f2, ?cs2) =>
      tryif constr_eq (f1, f2, po) (e1, e2, (r, o))
      then fail "radcan_pre: nothing to rewrite" else idtac;
      let c := lazymatch mode with
               | 0%N => eval vm_compute in (radcan_check f1 f2)
               | 1%N => eval vm_compute in (radcan_check_odd f1 f2)
               | 2%N => eval vm_compute in (radcan_check_neg f1 f2)
               | 3%N => eval vm_compute in (radcan_check_real f1 f2)
               end in
      lazymatch c with
      | Some ?cs =>
          lazymatch refined with
          | true =>
              let rcs := eval vm_compute in (refine (cs1 ++ cs2 ++ cs)) in
              lazymatch mode with
              | 0%N => apply: (@radcan_eq_pre_refined _ r env
                         radcan_fuel e1 e2 f1 f2 cs1 cs2 cs rcs)
              | 1%N => apply: (@radcan_eq_pre_refined_odd _ r env o
                         radcan_fuel e1 e2 f1 f2 cs1 cs2 cs rcs)
              | 2%N => apply: (@radcan_eq_pre_refined_neg _ r env o om hov
                         radcan_fuel e1 e2 f1 f2 cs1 cs2 cs rcs)
              | 3%N => apply: (@radcan_eq_pre_refined_real _ r env o
                         radcan_fuel e1 e2 f1 f2 cs1 cs2 cs rcs)
              end;
              [radcan_vm_refl | radcan_vm_refl
              | radcan_vm_refl | radcan_vm_refl
              | radcan_split_rconds]
          | false =>
              lazymatch mode with
              | 0%N => apply: (@radcan_eq_pre _ r env
                         radcan_fuel e1 e2 f1 f2 cs1 cs2 cs)
              | 1%N => apply: (@radcan_eq_pre_odd _ r env o
                         radcan_fuel e1 e2 f1 f2 cs1 cs2 cs)
              | 2%N => apply: (@radcan_eq_pre_neg _ r env o om hov
                         radcan_fuel e1 e2 f1 f2 cs1 cs2 cs)
              | 3%N => apply: (@radcan_eq_pre_real _ r env o
                         radcan_fuel e1 e2 f1 f2 cs1 cs2 cs)
              end;
              [radcan_vm_refl | radcan_vm_refl
              | radcan_vm_refl | radcan_split_conds]
          end
      | None => fail "radcan_pre: the normal forms differ"
      end end end
  end.

(* the (root, mode) used by radcan_plain_gen, tt without a root *)
Ltac radcan_plain_sel :=
  lazymatch goal with
  | |- context [proot ?r _ _] =>
      lazymatch goal with
      | rl : realroot r |- _ => constr:((r, rl))
      | o : oddroot r |- _ => constr:((r, o))
      | w : negroot r |- _ => constr:((r, w))
      | _ => constr:((r, tt))
      end
  | |- context [@nthroot ?C _ _] =>
      constr:((rootC_posroot C, rootC_negroot C))
  | |- context [@rootR ?R _ _] =>
      constr:((rootR_posroot R, rootR_realroot R))
  | _ => constr:(tt)
  end.

(* the dispatch of the fallback: omega_rw with a smallroot in context, and *)
(* always on n.-root goals (rootC_smallroot C); after: the plain check     *)
(* already failed on this goal                                             *)
Ltac radcan_pre_dispatch refined after :=
  rewrite ?normr_rootR;
  let po := lazymatch after with
            | true => radcan_plain_sel
            | false => constr:(tt)
            end in
  lazymatch goal with
  | |- context [proot ?r _ _] =>
      lazymatch goal with
      | rl : realroot r |- _ =>
          rewrite ?(normr_proot rl); radcan_pre_with_gen refined r rl tt po
      | o : oddroot r |- _ => radcan_pre_with_gen refined r o tt po
      | ov : @smallroot _ r ?w |- _ =>
          radcan_pre_with_gen refined r w ov po
      | w : negroot r |- _ => radcan_pre_with_gen refined r w tt po
      | _ => radcan_pre_with_gen refined r tt tt po
      end
  | |- context [@nthroot ?C _ _] =>
      radcan_pre_with_gen refined (rootC_posroot C) (rootC_negroot C)
        (rootC_smallroot C) po
  | |- context [@rootR ?R _ _] =>
      radcan_pre_with_gen refined (rootR_posroot R) (rootR_realroot R) tt po
  end.

Ltac radcan_pre_only refined := radcan_pre_dispatch refined false.

(* plain check first, so that the goals it proves keep their conditions *)
Ltac radcan_gen refined :=
  first [radcan_plain_gen refined | radcan_pre_dispatch refined true].

Ltac radcan_with r := radcan_with_gen true r tt.
Ltac radcan := radcan_gen true.
Ltac radcan_raw := radcan_gen false.
