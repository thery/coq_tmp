(* Pointing actions that show information on the selection instead of
   writing a line: actions of kind [show] (point_actions.v).  The
   interface displays the message that point_run (point_run_path) prints,
   and inserts nothing.

     Type of           t : T
     Check this        what Check t prints: t, then  : T  on its own line
     Normal form       t ⇒ v, v the full normal form (call by value, as
                       eval compute: coq.reduction.cbv.norm)
     Head normal form  t ⇒ v, v the weak head normal form (as eval hnf
                       up to the head: coq.reduction.lazy.whd)
     Where defined     the head constant (or variable) of the selection:
                       its full name, its kind, its library
     Unfolds to        t ⇒ v, one step of delta: the body of the head
                       constant applied to the arguments, beta-reduced

   Each works on a selection in the conclusion, in a hypothesis, under
   binders (the subterm is typed and printed under the binders crossed,
   with the names of the goal), and on a binder name (point_run_path, a
   path ending at the index 0 of a binder: point-action-names): the
   variable that the binder binds. *)

From coq_tmp Require Export point_actions.

Elpi Accumulate pbp_select.db lp:{{

kind show-sel type.
type sel-term term -> show-sel.           % a subterm
type sel-name term -> string -> show-sel. % a binder name: its variable and
                                          % the kind of its binder

% [show-sel In F S] S is what F says of the (first) selection of In: F Sel
% Bs S is run under the binders crossed on the way to the selection (in
% its part), Bs being the variables they bind with the kinds of the
% binders (forall, fun, let)
pred show-sel i:point-in,
              i:(pred i:show-sel, i:list (pair term string), o:string),
              o:string.
show-sel (point-in Names _ _ Parts [loc _ I P0 | _]) F S :-
  std.nth I Parts (part _ T _), show-names Names => show-walk P0 T [] F S.

% [show-names Ns] the names of the hypotheses and of the binders crossed
% (for display-names: the names the printer avoids)
pred show-names o:list string.

pred show-walk i:list int, i:term, i:list (pair term string),
               i:(pred i:show-sel, i:list (pair term string), o:string),
               o:string.
show-walk [] T Bs F S :- !, F (sel-term T) Bs S.
show-walk [0] T Bs F S :- binder-kind T K, !, show-bind T K Bs (x\ bs\ s\ F (sel-name x K) bs s) S.
show-walk [I|P] T Bs F S :- kids T Ks, std.nth I Ks Kd,
  (Kd = kt U, !, show-walk P U Bs F S ;
   (binder-kind T K, ! ; K = "cast"),
   show-bind T K Bs (x\ bs\ s\ sigma B\ (T = prod _ _ B ; T = fun _ _ B ; T = let _ _ _ B),
                       show-walk P (B x) bs F s) S).

% [show-bind T K Bs G S] G x Bs1 S under the binder T (of kind K), x its
% variable (declared: decl, or def for a let)
pred show-bind i:term, i:string, i:list (pair term string),
               i:(pred i:term, i:list (pair term string), o:string), o:string.
show-bind (prod N Ty _) K Bs G S :- !, with-name N (pi x\ decl x N Ty => G x [pr x K|Bs] S).
show-bind (fun N Ty _) K Bs G S :- !, with-name N (pi x\ decl x N Ty => G x [pr x K|Bs] S).
show-bind (let N Ty V _) K Bs G S :- with-name N (pi x\ def x N Ty V => G x [pr x K|Bs] S).

% [with-name N G] G, the name N added to show-names
pred with-name i:name, i:prop.
with-name N G :- show-names Ns, !, coq.name->id N S, (show-names [S|Ns] => G).

% [show-text T S] S is T printed on one line
pred show-text i:term, o:string.
show-text T S :- show-names Ns, !, text-at-names Ns bm-hyp [] T S.
show-text T S :- coq.term->string T S0, one-line S0 S.

% [sel-of Sel T] T is the selected term (the variable of a binder name)
pred sel-of i:show-sel, o:term.
sel-of (sel-term T) T.
sel-of (sel-name X _) X.

pred show-type i:show-sel, i:list (pair term string), o:string.
show-type Sel _ S :- sel-of Sel T, coq.typecheck T Ty ok, !,
  show-text T TS, show-text Ty TyS, S is TS ^ " : " ^ TyS.
show-type _ _ _ :- coq.ltac.fail 0 {msg "the selection has no type (it is not well typed alone)"}.

pred show-check i:show-sel, i:list (pair term string), o:string.
show-check Sel _ S :- sel-of Sel T, coq.typecheck T Ty ok, !,
  show-text T TS, show-text Ty TyS, S is TS ^ "\n     : " ^ TyS.
show-check _ _ _ :- coq.ltac.fail 0 {msg "the selection has no type (it is not well typed alone)"}.

pred show-norm i:show-sel, i:list (pair term string), o:string.
show-norm Sel _ S :- sel-of Sel T,
  coq.reduction.cbv.norm T V, show-text T TS, show-text V VS,
  S is TS ^ " ⇒ " ^ VS.

pred show-whd i:show-sel, i:list (pair term string), o:string.
show-whd Sel _ S :- sel-of Sel T,
  coq.reduction.lazy.whd T V, show-text T TS, show-text V VS,
  S is TS ^ " ⇒ " ^ VS.

% [sel-head T H] H is the head of T: T, or the function of the application T
pred sel-head i:term, o:term.
sel-head (app [H|_]) H :- !.
sel-head T T.

pred show-where i:show-sel, i:list (pair term string), o:string.
show-where (sel-name X K) _ S :- !,
  show-text X XS, S is XS ^ ": a variable bound by a " ^ K ^ " of the goal".
show-where (sel-term T) Bs S :- sel-head T H, where-head H Bs S, !.
show-where (sel-term T) _ _ :- show-text T TS,
  coq.ltac.fail 0 {msg "the selection has no head constant nor variable:"} TS.

pred where-head i:term, i:list (pair term string), o:string.
where-head H Bs S :- name H, std.lookup Bs H K, !,
  show-text H HS, S is HS ^ ": a variable bound by a " ^ K ^ " of the goal".
where-head H _ S :- name H, def H _ _ _, !,
  show-text H HS, S is HS ^ ": a local definition of the goal (a hypothesis x := v)".
where-head H _ S :- name H, !,
  show-text H HS, S is HS ^ ": a hypothesis of the goal (a local variable)".
where-head (global GR) _ S :- !, where-gref GR S.
where-head (pglobal GR _) _ S :- where-gref GR S.

pred where-gref i:gref, o:string.
where-gref GR S :-
  coq.gref->string GR Name, gref-kind GR Kind,
  coq.gref->path GR Path, std.string.concat "." Path Lib,
  S is Name ^ ": " ^ Kind ^ ", in the library " ^ Lib.

pred gref-kind i:gref, o:string.
gref-kind (indt _) "an inductive type".
gref-kind (indc _) "a constructor".
gref-kind (const C) "a lemma or an opaque definition (Qed)" :- coq.env.opaque? C, !.
gref-kind (const C) "an axiom or a parameter (no body)" :- coq.env.const C none _, !.
gref-kind (const _) "a definition".

pred show-unfold i:show-sel, i:list (pair term string), o:string.
show-unfold Sel _ S :- sel-of Sel T, unfold-head T C V, !,
  show-text T TS, show-text V VS, coq.gref->string (const C) CS,
  S is TS ^ " ⇒ " ^ VS ^ "  (" ^ CS ^ " unfolded)".
show-unfold Sel _ _ :- sel-of Sel T, sel-head T H,
  (H = global (const C) ; H = pglobal (const C) _), !,
  coq.gref->string (const C) CS,
  coq.ltac.fail 0 {msg "the constant"} CS "has no body to unfold (opaque, an axiom)".
show-unfold _ _ _ :-
  coq.ltac.fail 0 {msg "the selection is not a constant nor an application of a constant"}.

% [unfold-head T C V] V is T where its head constant C is replaced by its
% body, beta-reduced (coq.mk-app reduces a head fun)
pred unfold-head i:term, o:constant, o:term.
unfold-head T C V :-
  sel-head T H, (H = global (const C) ; H = pglobal (const C) _),
  not (coq.env.opaque? C), coq.env.const C (some B) _,
  (T = app [_|Args], ! ; Args = []), coq.mk-app B Args V.

% the actions, of kind show; they take binder names (point-action-names)
point-action "Type of" show "show the type of the selection: t : T"
  (in\ s\ show-sel in show-type s).
point-action "Check this" show "show what Check prints for the selection"
  (in\ s\ show-sel in show-check s).
point-action "Normal form" show "show the normal form of the selection (eval compute): t ⇒ v"
  (in\ s\ show-sel in show-norm s).
point-action "Head normal form" show "show the weak head normal form of the selection: t ⇒ v"
  (in\ s\ show-sel in show-whd s).
point-action "Where defined" show "show the head constant or variable of the selection: its full name, its kind, its library"
  (in\ s\ show-sel in show-where s).
point-action "Unfolds to" show "show one unfolding of the head constant of the selection: t ⇒ v"
  (in\ s\ show-sel in show-unfold s).
point-action-names "Type of".
point-action-names "Check this".
point-action-names "Normal form".
point-action-names "Head normal form".
point-action-names "Where defined".
point-action-names "Unfolds to".
}}.
