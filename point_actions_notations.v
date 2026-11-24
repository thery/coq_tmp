(* Pointing actions on the notations of the goal display.

     Disable notation    (point) on a subterm printed with a notation:
                         Disable Notation := (H _ .. _) (all).
     Enable notation     (point) on a subterm printed in prefix form:
                         Enable Notation := (H _ .. _) (all).
     Without notations   (show) the selection printed with Printing
                         Notations off (the other options at their
                         default)

   H is the head constant (or inductive, constructor) of the selection,
   with one _ per explicit argument the selection gives it (the implicit
   ones are left out: Disable Notation := (eq _ _) is the notation of
   x = y).  (all) disables or enables all the notations of that
   interpretation: x = y and x = y :> A for eq, ~ x but also x <> y for
   not (Rocq refuses the line without (all) when there are several).

   Whether the selection is printed with a notation is told by printing
   its head applied to new variables (so that its arguments print as
   names), with and without Printing Notations.  Rocq-Elpi cannot ask
   which notations are disabled: Enable notation is offered on any
   selection printed in prefix form; when no notation of that
   interpretation was disabled, the line only warns (Found no matching
   notation to enable or disable). *)

From coq_tmp Require Export point_actions point_actions_show.

Elpi Accumulate pbp_select.db lp:{{

% [notation-head T H GR Args] the selection T is the application of the
% global GR (the term H) to Args (none: GR alone)
pred notation-head i:term, o:term, o:gref, o:list term.
notation-head T H GR Args :-
  (T = app [H|Args], ! ; H = T, Args = []),
  (H = global GR ; H = pglobal GR _), !.
notation-head _ _ _ _ :-
  coq.ltac.fail 0 {msg "the selection is not a constant, an inductive or a constructor applied to arguments"}.

% [with-notations B G] G with Printing Notations set to B (and Printing
% All, Implicit, Coercions unset), then the options put back
pred with-notations i:bool, i:prop.
with-notations B G :-
  Off = [["Printing", "All"], ["Printing", "Implicit"], ["Printing", "Coercions"]],
  On = ["Printing", "Notations"],
  std.map Off (o\ v\ coq.option.get o v) OldOff, coq.option.get On OldOn,
  std.forall Off (o\ coq.option.set o (coq.option.bool ff)),
  coq.option.set On (coq.option.bool B),
  (G, !, R = tt ; R = ff),
  std.forall2 Off OldOff (o\ v\ coq.option.set o v), coq.option.set On OldOn,
  R = tt.

% [skeleton-printed-with-notation H N] H applied to N new variables
% prints differently with and without notations: it is printed with a
% notation
pred skeleton-printed-with-notation i:term, i:int.
skeleton-printed-with-notation H N :- skeleton-texts H N [] S1 S2, not (S1 = S2).

pred skeleton-texts i:term, i:int, i:list term, o:string, o:string.
skeleton-texts H 0 Xs S1 S2 :- !,
  coq.mk-app H Xs T,
  with-notations tt (coq.term->string T S1), with-notations ff (coq.term->string T S2).
skeleton-texts H N Xs S1 S2 :- N1 is N - 1,
  std.length Xs K, Nm is "pbp_arg" ^ int_to_string K, coq.id->name Nm Name,
  pi x\ decl x Name {{ Prop }} => sigma Xs1\ std.append Xs [x] Xs1,
    skeleton-texts H N1 Xs1 S1 S2.

% [explicit-holes GR Args S] S is "_ _ .. _", one _ per argument of Args
% that is explicit for GR
pred explicit-holes i:gref, i:list term, o:string.
explicit-holes GR Args S :-
  (coq.arguments.implicit GR [Imps|_], ! ; Imps = []),
  std.length Args N, std.iota N Is,
  std.length Imps NI,
  std.filter Is (i\ not (i < NI, std.nth i Imps K, (K = implicit ; K = maximal))) Es,
  std.map Es (_\ s\ s = "_") Hs, std.string.concat " " Hs S.

% [gref-short-name GR S] S is the shortest name of GR that Rocq resolves
% to GR (its identifier, else its full name)
pred gref-short-name i:gref, o:string.
gref-short-name GR S :-
  coq.gref->string GR Full, rex.split "\\." Full Parts, std.rev Parts RParts,
  short-suffix RParts [] GR S, !.
gref-short-name GR S :- coq.gref->string GR S.

% [short-suffix Rs Acc GR S] S is the shortest suffix of the qualified
% name (its components reversed: Rs) that Rocq resolves to GR only
pred short-suffix i:list string, i:list string, i:gref, o:string.
short-suffix [P|Rs] Acc GR S :- Acc1 = [P|Acc], std.string.concat "." Acc1 S1,
  (coq.locate-all S1 [loc-gref GR], !, S = S1 ; short-suffix Rs Acc1 GR S).

% [notation-line What In Line] the line Disable or Enable (What) of the
% notation of the selection (under the binders crossed, as the show
% actions: show-sel)
pred notation-line i:string, i:point-in, o:string.
notation-line What In Line :- show-sel In (notation-line-of What) Line.

pred notation-line-of i:string, i:show-sel, i:list (pair term string), o:string.
notation-line-of What Sel _ Line :-
  sel-of Sel T, notation-head T H GR Args, std.length Args N,
  (What = "Disable", !,
   (skeleton-printed-with-notation H N, ! ;
    coq.ltac.fail 0 {msg "the selection is not printed with a notation (its head is printed in prefix form)"}) ;
   (not (skeleton-printed-with-notation H N), ! ;
    coq.ltac.fail 0 {msg "the selection is printed with a notation already"})),
  explicit-holes GR Args Hs, gref-short-name GR Name,
  (Hs = "", !, Pat = Name ; Pat is Name ^ " " ^ Hs),
  Line is What ^ " Notation := (" ^ Pat ^ ") (all).".

% [without-notations In S] S is the selection printed without notations
% (under the binders crossed, as the show actions: show-sel)
pred without-notations i:point-in, o:string.
without-notations In S :- show-sel In show-without S.

pred show-without i:show-sel, i:list (pair term string), o:string.
show-without Sel _ S :- sel-of Sel T, with-notations ff (show-text T S).

point-action "Disable notation" point
  "write Disable Notation := (f _ .. _) (all). for the notation the selection is printed with"
  (notation-line "Disable").
point-action "Enable notation" point
  "write Enable Notation := (f _ .. _) (all). for a selection printed in prefix form (its notation disabled)"
  (notation-line "Enable").
point-action "Without notations" show
  "show the selection printed without notations"
  without-notations.
point-action-names "Without notations".
point-action-any-subterm "Disable notation".
point-action-any-subterm "Enable notation".
}}.
