(******************************************************************************)
(* SimplifyTac: radcan_simplify, the analogue of ring_simplify.               *)
(*   radcan_simplify        == simplifies both sides of the goal a = b,       *)
(*                             a <= b, a < b, a == b, a != b or a <> b        *)
(*   radcan_simplify in H   == the same in the hypothesis H                   *)
(*   radcan_simplify_term t == simplifies t and rewrites it in the goal       *)
(*   radcan_simplify_raw, radcan_simplify_raw in H,                           *)
(*   radcan_simplify_term_raw t == the same with the raw side conditions      *)
(* Each side is reified (Tactic.v), its normal form is printed back           *)
(* (Simplify.v) and shown with numerals k%:R, n.-root (on C), rootR (on a     *)
(* real closed field) or proot r.  The atoms are numbered in their order of   *)
(* appearance in the result (up to 3 rounds), so that simplifying again       *)
(* gives the same term.  The equality with the original side is proved by     *)
(* the radcan checker; its side conditions are left as goals after the main   *)
(* goal (refined as by radcan, Refine.v).  The root structure and the mode    *)
(* are chosen as by radcan: proot r (with a realroot / oddroot / negroot of   *)
(* r in the context if any), n.-root (negroot), rootR (realroot), root-free.  *)
(* Real mode: `|a| is read as rootR 2 (a ^+ 2) (or proot r 2 (a ^+ 2)) and    *)
(* printed back as `|a|.                                                      *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC RootR Syntax Radcan Refine OddRoot.
From Radcan Require Import NegRootC RealRoot AbsRoot Tactic Simplify.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* (mode, r, o): 0 generic, 1 odd (o : oddroot r), 2 neg (o : negroot r),
   3 root-free, 4 real (o : realroot r) *)
Ltac rs_root t :=
  lazymatch t with
  | context [proot ?r _ _] =>
      lazymatch goal with
      | rl : realroot r |- _ => constr:((4%N, r, rl))
      | o : oddroot r |- _ => constr:((1%N, r, o))
      | w : negroot r |- _ => constr:((2%N, r, w))
      | _ => constr:((0%N, r, tt))
      end
  | context [@nthroot ?C _ _] =>
      constr:((2%N, rootC_posroot C, rootC_negroot C))
  | context [@rootR ?R _ _] =>
      constr:((4%N, rootR_posroot R, rootR_realroot R))
  | _ => constr:((3%N, tt, tt))
  end.

(* `|a| encoded as rootR 2 (a ^+ 2) on an rcfType, as proot r 2 (a ^+ 2)
   with a realroot r in the context (normr_rootR, normr_proot) *)
Ltac rs_abs_eq a :=
  match goal with
  | _ => constr:(normr_rootR a)
  | rl : realroot _ |- _ => constr:(normr_proot rl a)
  end.

Ltac rs_abs t :=
  match t with
  | context C [`|?a|] =>
      let h := rs_abs_eq a in
      lazymatch type of h with
      | _ = ?b => let t := context C [b] in rs_abs t
      end
  | _ => t
  end.

(* numerals pos2F p as k%:R (1 as 1), small indices as nat literals,
   roots of the instances as n.-root and rootR *)
Ltac rs_pretty t :=
  match t with
  | context C [pos2F ?F ?p] =>
      let x := lazymatch eval vm_compute in (Pos.leb p 100000) with
               | true =>
                   let n := eval vm_compute in (Pos.to_nat p) in
                   lazymatch n with
                   | 1%N => constr:(1 : F)
                   | _ => constr:(n%:R : F)
                   end
               | false => constr:((Pos.to_nat p)%:R : F)
               end in
      let t := context C [x] in rs_pretty t
  | context C [Pos.to_nat ?p] =>
      lazymatch eval vm_compute in (Pos.leb p 1000) with
      | true =>
          let n := eval vm_compute in (Pos.to_nat p) in
          let t := context C [n] in rs_pretty t
      end
  | context C [proot (rootC_posroot ?K) ?n ?x] =>
      let t := context C [@nthroot K n x] in rs_pretty t
  | context C [proot (rootR_posroot ?R) ?n ?x] =>
      let t := context C [@rootR R n x] in rs_pretty t
  | context C [@rootR ?R 2 (?a ^+ 2)] =>
      let t := context C [`|a|] in rs_pretty t
  | context C [proot ?r 2 (?a ^+ 2)] =>
      lazymatch goal with
      | _ : realroot r |- _ => let t := context C [`|a|] in rs_pretty t
      end
  | _ => t
  end.

(* (t', (mode, r, o, env, e, e', cs)): t' the simplified t, the atoms
   numbered from env0 *)
Ltac rs_info_env t env0 :=
  let t := rs_abs t in
  lazymatch rs_root t with
  | (?mode, ?r, ?o) =>
      let p := radcan_reify_term r t env0 in
      lazymatch p with
      | (?e, ?env) =>
          let res := lazymatch mode with
                     | 1%N => eval vm_compute in (radcan_simpl_odd e)
                     | 2%N => eval vm_compute in (radcan_simpl_neg e)
                     | 4%N => eval vm_compute in (radcan_simpl_real e)
                     | _ => eval vm_compute in (radcan_simpl e)
                     end in
          lazymatch res with
          | Some (?e', ?cs) =>
              let v := lazymatch mode with
                       | 3%N => constr:(rinterp0 env e')
                       | _ => constr:(rinterp r env e')
                       end in
              let v := eval cbv beta iota zeta delta [rinterp_gen Z2F nth]
                       in v in
              let t' := rs_pretty v in
              constr:((t', (mode, r, o, env, e, e', cs)))
          | None => fail "radcan_simplify: no stable normal form"
          end
      end
  end.

(* the atoms numbered in their order in the result (at most n rounds), so
   that simplifying the result again gives it back *)
Ltac rs_info_loop t i n :=
  lazymatch n with
  | O => i
  | S ?n =>
      lazymatch i with
      | (?t1, (_, ?r, _, _, _, _, _)) =>
          let T := type of t in
          let t1a := rs_abs t1 in
          let p := radcan_reify_term r t1a (@nil T) in
          lazymatch p with
          | (_, ?env1) =>
              let i2 := rs_info_env t env1 in
              lazymatch i2 with
              | (t1, _) => i2
              | _ => rs_info_loop t i2 n
              end
          end
      end
  end.

Ltac rs_info t :=
  let T := type of t in
  let i := rs_info_env t (@nil T) in
  rs_info_loop t i 3%N.

(* proves t = t' from rs_info, leaving the side conditions *)
Ltac rs_prove refined info :=
  lazymatch info with
  | (_, (?mode, ?r, ?o, ?env, ?e, ?e', ?cs)) =>
      lazymatch mode with
      | 3%N => change (rinterp0 env e = rinterp0 env e')
      | 4%N =>
          rewrite ?(normr_proot o); change (rinterp r env e = rinterp r env e')
      | _ => change (rinterp r env e = rinterp r env e')
      end;
      lazymatch refined with
      | true =>
          let rcs := eval vm_compute in (refine cs) in
          lazymatch mode with
          | 0%N => apply: (@radcan_simpl_sound _ r env e e' cs rcs)
          | 1%N => apply: (@radcan_simpl_sound_odd _ r o env e e' cs rcs)
          | 2%N => apply: (@radcan_simpl_sound_neg _ r o env e e' cs rcs)
          | 4%N => apply: (@radcan_simpl_sound_real _ r o env e e' cs rcs)
          | 3%N =>
              apply: (@radcan_simpl_sound0 _ env e e' cs rcs erefl erefl)
          end;
          [vm_compute; reflexivity | vm_compute; reflexivity
          | radcan_split_rconds]
      | false =>
          lazymatch mode with
          | 0%N => apply: (@radcan_simpl_cond _ r env e e' cs)
          | 1%N => apply: (@radcan_simpl_cond_odd _ r o env e e' cs)
          | 2%N => apply: (@radcan_simpl_cond_neg _ r o env e e' cs)
          | 4%N => apply: (@radcan_simpl_cond_real _ r o env e e' cs)
          | 3%N => apply: (@radcan_simpl_cond0 _ env e e' cs erefl erefl)
          end;
          [vm_compute; reflexivity | radcan_split_conds]
      end
  end.

Ltac rs_term refined t :=
  let info := rs_info t in
  lazymatch info with
  | (?t', _) =>
      let H := fresh "Hsimpl" in
      cut (t = t'); [move=> H; rewrite H; clear H | rs_prove refined info]
  end.

(* both sides of a relation: goal R a b *)
Ltac rs_rel refined lem R a b :=
  let ia := rs_info a in
  let ib := rs_info b in
  lazymatch ia with
  | (?a', _) =>
      lazymatch ib with
      | (?b', _) =>
          apply: (@lem _ R a a' b b');
            [idtac | rs_prove refined ia | rs_prove refined ib]
      end
  end.

Ltac rs_goal refined :=
  lazymatch goal with
  | |- @eq ?T ?a ?b => rs_rel refined simpl_rel (@eq T) a b
  | |- ~ (@eq ?T ?a ?b) =>
      rs_rel refined simpl_rel (fun x y : T => ~ (x = y)) a b; [cbv beta|..]
  | |- is_true (~~ (@eq_op ?T ?a ?b)) =>
      rs_rel refined simpl_brel (fun x y : T => x != y) a b; [cbv beta|..]
  | |- is_true (?R ?a ?b) => rs_rel refined simpl_brel R a b
  | _ => fail "radcan_simplify: the goal is not a relation"
  end.

(* hypothesis H : R a b *)
Ltac rs_hrel refined lem R a b H :=
  let ia := rs_info a in
  let ib := rs_info b in
  lazymatch ia with
  | (?a', _) =>
      lazymatch ib with
      | (?b', _) =>
          let P := constr:(R a' b') in
          let P := lazymatch type of P with
                   | bool => constr:(is_true P)
                   | _ => P
                   end in
          cut P;
            [clear H; intro H
            | apply: (@lem _ R a a' b b');
                [rs_prove refined ia | rs_prove refined ib | exact: H]]
      end
  end.

Ltac rs_hyp refined H :=
  lazymatch type of H with
  | @eq ?T ?a ?b => rs_hrel refined simpl_rel_hyp (@eq T) a b H
  | ~ (@eq ?T ?a ?b) =>
      rs_hrel refined simpl_rel_hyp (fun x y : T => ~ (x = y)) a b H;
        [cbv beta in H|..]
  | is_true (~~ (@eq_op ?T ?a ?b)) =>
      rs_hrel refined simpl_brel_hyp (fun x y : T => x != y) a b H;
        [cbv beta in H|..]
  | is_true (?R ?a ?b) => rs_hrel refined simpl_brel_hyp R a b H
  | _ => fail "radcan_simplify: the hypothesis is not a relation"
  end.

Tactic Notation "radcan_simplify" := rs_goal true.
Tactic Notation "radcan_simplify_raw" := rs_goal false.
Tactic Notation "radcan_simplify" "in" hyp(H) := rs_hyp true H.
Tactic Notation "radcan_simplify_raw" "in" hyp(H) := rs_hyp false H.
Tactic Notation "radcan_simplify_term" constr(t) := rs_term true t.
Tactic Notation "radcan_simplify_term_raw" constr(t) := rs_term false t.
