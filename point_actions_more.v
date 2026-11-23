(* More pointing actions, beside Point and Link (point_actions.v): actions
   that change the selected subterm only, in the conclusion or in the
   hypothesis it is in.  The demos and the tests load this file; the
   tutorial (point_actions_tutorial.v) does not: it writes its own
   Simplify and Unfold in Elpi. *)

From coq_tmp Require Export point_actions.

PointAction "Simplify here" point "{pre:in}rewrite {local:pbp}/={post:in}."
  "simplify the selected subterm (ssreflect's rewrite /=, at the selection)".
PointAction "Unfold here" point "{pre:in}rewrite {local:pbp}/{head}{post:in}."
  "unfold the constant at the head of the selected subterm, in it".
PointAction "Name occurrence" point "{pre:in}set x := {local:occ}({text}){post:in}."
  "name x this occurrence of the selected subterm (ssreflect's set x := {n}(t))".
