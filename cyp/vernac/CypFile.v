(* Cyp File "proof.md": a cyp proof written in Markdown, read and checked
   inside Rocq; the formulas between backticks are parsed by Rocq
   (coq.parse.argument, Rocq-Elpi >= the coq-parse-argument branch), in the
   context of their step.  The lemma is defined when every step is proved.

   The file is the Markdown of cyp (see ../README.md): a header between two
   lines "---" (only its field [scope:] is used here: the delimiter of the
   scope of the formulas, e.g. Z or R), a title "# name", the statement
   (Let `vars`. If `hyps` then `goal`.) and one list item per step.  The
   libraries and the rules are loaded by the .v file before the command.

   Not yet: nested steps and local scopes, [by:], [rules:], the checked
   Markdown output (the steps are reported by messages). *)

From Stdlib Require Import PrimString List.
From elpi Require Import elpi.
Require Import Cyp.

Elpi Command CypFile.
Elpi Accumulate Db cyp.db.
Elpi Accumulate File cyp_core.
Elpi Accumulate lp:{{

  % ---------------------------------------------------------------- %
  % Reading the file

  pred read-lines i:string, o:list string.
  read-lines F L :- open_in F I, read-all I L, close_in I.

  pred read-all i:in_stream, o:list string.
  read-all I [] :- eof I, !.
  read-all I [X | L] :- input_line I X, read-all I L.

  % the lines of the title and of the list items
  pred title-line i:string.
  title-line L :- rex.match "^# " L.
  pred item-line i:string.
  item-line L :- rex.match "^ *[-*] " L.

  % [from-title L R]: R is L from its title line
  pred from-title i:list string, o:list string.
  from-title [] [].
  from-title [X | L] [X | L] :- title-line X, !.
  from-title [_ | L] R :- from-title L R.

  % [until-item L A B]: L = A ++ B, B starting at the first list item
  pred until-item i:list string, o:list string, o:list string.
  until-item [] [] [].
  until-item [X | L] [] [X | L] :- item-line X, !.
  until-item [X | L] [X | A] B :- until-item L A B.

  pred trim i:string, o:string.
  trim S T :- rex.replace "^[ \t]+" "" S S1, rex.replace "[ \t]+$" "" S1 T.

  % the header: the lines between the first two lines "---"
  pred header i:list string, o:list string, o:list string.
  header [L | R] H B :- trim L "---", !, take-header R H B.
  header L [] L.
  pred take-header i:list string, o:list string, o:list string.
  take-header [L | R] [] R :- trim L "---", !.
  take-header [L | R] [L | H] B :- take-header R H B.
  take-header [] [] [].

  pred field i:list string, i:string, o:string.
  field H K V :-
    Re is "^ *" ^ K ^ ":", Re1 is "^ *" ^ K ^ ": *",
    std.mem H L, rex.match Re L, !,
    rex.replace Re1 "" L V0, trim V0 V.
  field _ _ "".

  % the title, the statement and the steps of the proof
  pred body i:list string, o:string, o:string, o:list string.
  body Ls Name Stmt Steps :-
    from-title Ls [T | R],
    rex.replace "^# *" "" T Name0, trim Name0 Name,
    until-item R S Items,
    std.filter S (l\ sigma t\ trim l t, not (t = "")) S1,
    std.map S1 trim S2, std.string.concat " " S2 Stmt,
    items-of Items Steps.

  % one string per list item, continuation lines joined
  pred items-of i:list string, o:list string.
  items-of [] [].
  items-of [L | R] [It | Its] :-
    rex.replace "^ *[-*] +" "" L L1,
    until-item R Cont R1,
    std.map Cont trim Cont1, std.string.concat " " [L1 | Cont1] It0, trim It0 It,
    items-of R1 Its.

  % ---------------------------------------------------------------- %
  % Words and formulas: the text between backticks is a formula

  kind piece type.
  type ptext string -> piece.
  type pform string -> piece.

  pred pieces i:string, o:list piece.
  pieces S P :- N is size S, chars S 0 N "" ff P.

  % [chars S I N Acc InFormula P]: the pieces of S from position I
  pred chars i:string, i:int, i:int, i:string, i:bool, o:list piece.
  chars _ N N Acc F P :- !, last-piece Acc F P.
  chars S I N Acc F P :-
    C is substring S I 1, I1 is I + 1,
    if (C = "`")
       (flush Acc F P P1, (F = tt, F1 = ff ; F = ff, F1 = tt), !,
        chars S I1 N "" F1 P1)
       (Acc1 is Acc ^ C, chars S I1 N Acc1 F P).

  pred flush i:string, i:bool, o:list piece, o:list piece.
  flush "" _ P P :- !.
  flush A ff [ptext A | P] P.
  flush A tt [pform A | P] P.
  pred last-piece i:string, i:bool, o:list piece.
  last-piece "" _ [] :- !.
  last-piece A ff [ptext A].
  last-piece A tt [pform A].

  % ---------------------------------------------------------------- %
  % Parsing the formulas, in the current context

  % a formula of a step: a term, or a mention that does not parse (shown,
  % not checked) -- its error is reported
  pred parse-formula i:string, i:string, o:item.
  parse-formula Scope S (formula T) :-
    coq.parse.argument {calc ("(" ^ S ^ ")")} ff Scope (trm T) ok, !.
  parse-formula _ S (word Q) :- Q is "`" ^ S ^ "`".

  pred step-items i:string, i:list piece, o:list item.
  step-items _ [] [].
  step-items Sc [ptext W | P] [word W | L] :- step-items Sc P L.
  step-items Sc [pform F | P] [I | L] :- parse-formula Sc F I, step-items Sc P L.

  % ---------------------------------------------------------------- %
  % The statement: Let `vars`. If `hyps` then `goal`.

  kind srole type.
  type svar, shyp, sgoal srole.

  % the role of each formula of the statement, by the word before it
  pred statement-roles i:list piece, i:srole, o:list (pair srole string).
  statement-roles [] _ [].
  statement-roles [ptext W | P] R L :-
    words-rev W Ws,
    (std.mem Ws X, srole-word X R1, ! ; R1 = R),
    statement-roles P R1 L.
  statement-roles [pform F | P] R [pr R F | L] :- statement-roles P R L.

  pred srole-word o:string, o:srole.
  srole-word "let" svar.  srole-word "if" shyp.  srole-word "assume" shyp.
  srole-word "then" sgoal. srole-word "show" sgoal.

  % [statement Scope Roles Ty Proof Steps Ko]: the lemma's type Ty, and its
  % proof from the steps, under the variables and hypotheses
  % the steps are parsed at the end, in the full context of the statement
  pred statement i:int, i:string, i:list (pair srole string), i:list (list piece),
    o:term, o:term, o:list string.
  statement K Sc [pr svar V | R] Steps Ty P Ko :- !,
    std.assert-ok! (coq.parse.argument {calc ("Context (" ^ V ^ ")")} ff "" (ctx-decl C))
      "cyp: a variable of the statement does not parse",
    binders K Sc C R Steps Ty P Ko.
  % the hypotheses are named H1, H2, ...
  statement K Sc [pr shyp H | R] Steps (prod Nm T TyR) (fun Nm T PR) Ko :- !,
    std.assert-ok! (coq.parse.argument {calc ("(" ^ H ^ ")")} ff Sc (trm T))
      "cyp: a hypothesis of the statement does not parse",
    K1 is K + 1, coq.id->name {calc ("H" ^ {std.any->string K1})} Nm,
    pi h\ decl h Nm T => statement K1 Sc R Steps (TyR h) (PR h) Ko.
  statement _ Sc [pr sgoal G | _] StepPieces T P Ko :-
    std.assert-ok! (coq.parse.argument {calc ("(" ^ G ^ ")")} ff Sc (trm T))
      "cyp: the conclusion of the statement does not parse",
    std.map StepPieces (step-items Sc) Steps,
    skel 0 Steps T P Ko.

  pred binders i:int, i:string, i:context-decl, i:list (pair srole string),
    i:list (list piece), o:term, o:term, o:list string.
  binders K Sc context-end R Steps Ty P Ko :- statement K Sc R Steps Ty P Ko.
  binders K Sc (context-item N _ T _ C) R Steps (prod Nm T TyR) (fun Nm T PR) Ko :-
    coq.id->name N Nm,
    pi x\ decl x Nm T => binders K Sc (C x) R Steps (TyR x) (PR x) Ko.

  % ---------------------------------------------------------------- %

  main [str F] :-
    read-lines F Ls,
    header Ls H B, field H "scope" Sc,
    body B Name Stmt StepTexts,
    pieces Stmt SP, statement-roles SP sgoal Roles,
    coq.say "cyp:" Name,
    % the steps are parsed inside the context, by [statement]: they are
    % kept as texts until then
    std.map StepTexts pieces StepPieces,
    statement 0 Sc Roles StepPieces Ty Proof Ko,
    if (Ko = [])
       (std.assert-ok! (coq.typecheck Proof Ty) "cyp: the proof does not type-check",
        coq.env.add-const Name Proof Ty @opaque! _, coq.say "cyp:" Name "proved")
       (std.length Ko N, coq.error "cyp:" N "step(s) of" Name "not proved").
}}.
