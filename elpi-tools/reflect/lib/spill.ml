(* Desugaring of spilling: {f X} stands for the output of f X.

   As Elpi's compiler does it, a spilled call is replaced by a fresh
   variable V, and the goal f X V runs just before the goal that contained
   the spill; for a spill in the head of a rule, at the start of the body.
   Nested spills {f {g X}} run inner first.  The connectives , ; pi sigma =>
   ==> are looked through, so that the spilled goal stays under the pi that
   binds its variables.

   Not handled (left as written): a spill under a lambda inside an atom
   (e.g. in the predicate given to std.map) and a spill in the hypothesis of
   an implication.  [unhandled] tells whether a term still has spills. *)

open Elpi_parser.Ast

let mk loc it = { Term.it; loc }
let const loc name = mk loc (Term.Const (Func.from_string name))

let is_spill (t : Term.t) =
  match t.it with
  | Term.App ({ it = Term.Const c; _ }, [ _ ]) -> Func.equal c Func.spillf
  | _ -> false

let rec unhandled (t : Term.t) =
  is_spill t
  || match t.it with
     | Term.App (hd, args) -> unhandled hd || List.exists unhandled args
     | Term.Lam (_, _, _, b) -> unhandled b
     | Term.Cast (t, _) | Term.Parens t -> unhandled t
     | _ -> false

(* A counter of fresh variables, one per rule *)
type fresh = { mutable next : int }

let fresh_var counter loc =
  counter.next <- counter.next + 1;
  const loc (Printf.sprintf "Spill_%d" counter.next)

(* [call_with_output g v]: the goal g with v as extra last argument *)
let call_with_output (g : Term.t) (v : Term.t) : Term.t =
  match g.it with
  | Term.App (hd, args) -> mk g.loc (Term.App (hd, args @ [ v ]))
  | Term.Parens { it = Term.App (hd, args); _ } -> mk g.loc (Term.App (hd, args @ [ v ]))
  | _ -> mk g.loc (Term.App (g, [ v ]))

(* [lift counter t] replaces the spills of [t] (outside lambdas) by fresh
   variables; it returns the goals to run first, in order, and the new term. *)
let rec lift counter (t : Term.t) : Term.t list * Term.t =
  match t.it with
  | Term.App ({ it = Term.Const c; _ }, [ g ]) when Func.equal c Func.spillf ->
      let before, g = lift counter g in
      let v = fresh_var counter t.loc in
      (before @ [ call_with_output g v ], v)
  | Term.App (hd, args) ->
      let b1, hd = lift counter hd in
      let bs, args = List.split (List.map (lift counter) args) in
      (b1 @ List.concat bs, mk t.loc (Term.App (hd, args)))
  | Term.Cast (u, ty) ->
      let b, u = lift counter u in
      (b, mk t.loc (Term.Cast (u, ty)))
  | Term.Parens u ->
      let b, u = lift counter u in
      (b, mk t.loc (Term.Parens u))
  | _ -> ([], t)

let conj loc = function
  | [ g ] -> g
  | gs -> mk loc (Term.App (const loc ",", gs))

let is_const name (t : Term.t) =
  match t.it with Term.Const c -> Func.show c = name | _ -> false

(* [goal counter g]: the goal [g] with its spills desugared *)
let rec goal counter (g : Term.t) : Term.t =
  match g.it with
  | Term.App (hd, args) when is_const "," hd || is_const ";" hd ->
      mk g.loc (Term.App (hd, List.map (goal counter) args))
  | Term.App (hd, [ { it = Term.Lam (x, xl, ty, body); loc } ]) when is_const "pi" hd || is_const "sigma" hd ->
      mk g.loc (Term.App (hd, [ mk loc (Term.Lam (x, xl, ty, goal counter body)) ]))
  | Term.App (hd, [ hyp; concl ]) when is_const "=>" hd || is_const "==>" hd ->
      mk g.loc (Term.App (hd, [ hyp; goal counter concl ]))
  | Term.Parens u -> goal counter u
  | _ ->
      let before, g' = lift counter g in
      conj g.loc (before @ [ g' ])

(* [rule head body]: the rule with its spills desugared; the spills of the
   head go first in the body *)
let rule (head : Term.t) (body : Term.t) : Term.t * Term.t =
  let counter = { next = 0 } in
  let before, head = lift counter head in
  let body = goal counter body in
  let body =
    match before with
    | [] -> body
    | _ -> conj body.loc (before @ [ body ])
  in
  (head, body)
