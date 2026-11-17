(* Cyp: a proof written as text, checked step by step, inside Rocq.

     Cyp Lemma name binders : statement :=
       [ "words" (formula) "words" (formula) ... ;
         ... ].

   The body is a list of steps; a step mixes words (primitive strings) and
   formulas.  The words before a formula give its role, as in the Markdown
   cyp: a claim (after "we have", "hence", "show"...), a fact (after
   "from", "using", "since"), shown but not checked.  A step whose words
   say "suffices" or "equivalent to prove" goes backwards: its claim
   replaces the goal.

   Each step becomes one hole of a proof skeleton
     fun binders => let c1 : C1 := ?1 in let c2 : C2 := ?2 in ... ?n
   elaborated by Rocq, so that each hole has exactly the context of its
   step; the rules of cyp.db, then the default tactics, close the holes.
   When every step is closed, the lemma is defined; otherwise the command
   fails and says which steps are not proved. *)

From Stdlib Require Import PrimString List Lia Lra.
From elpi Require Import elpi.

(* The default tactics, tried in order on a step that no rule closes;
   a proof file may add others with [Elpi Accumulate cyp.db]. *)
Ltac cyp_tauto := tauto.
Ltac cyp_lia := lia.
Ltac cyp_nia := nia.
Ltac cyp_lra := lra.

Elpi Db cyp.db lp:{{
  % [justify Pattern Tac]: on a goal that matches Pattern, try Tac:
  % [ltac "name"], an Ltac tactic that must close the goal, or [lemma T],
  % refine with T, then close each premise with the rules again
  kind cyptac type.
  type ltac string -> cyptac.
  type lemma term -> cyptac.
  pred justify i:term, o:cyptac.

  % the tactics tried when no rule closes a step
  pred default-ltac o:string.
  default-ltac "cyp_tauto".
  default-ltac "cyp_lia".
  default-ltac "cyp_nia".
  default-ltac "cyp_lra".

  % [role-word W R]: a formula after the word W has the role R
  kind role type.
  type claim, fact role.
  pred role-word o:string, o:role.
  role-word "have" claim.   role-word "hence" claim.  role-word "so" claim.
  role-word "then" claim.   role-word "show" claim.   role-word "prove" claim.
  role-word "thus" claim.   role-word "get" claim.    role-word "deduce" claim.
  role-word "is" claim.     role-word "obtain" claim. role-word "as" claim.
  role-word "from" fact.    role-word "using" fact.   role-word "since" fact.
  role-word "because" fact. role-word "for" fact.

  % [backward-word W]: a step whose words contain W goes backwards
  pred backward-word o:string.
  backward-word "suffices". backward-word "enough".
  backward-word "equivalent". backward-word "written".
}}.

Ltac cyp_intros := progress intros.
Ltac cyp_split := split.
Ltac cyp_left := left.
Ltac cyp_right := right.

#[arguments(raw)] Elpi Command Cyp.
Elpi Accumulate Db cyp.db.
Elpi Accumulate lp:{{

  % ---------------------------------------------------------------- %
  % Closing a goal: the rules, then the default tactics

  pred close i:goal.
  close (goal _ _ {{ _ /\ _ }} _ _ as G) :-
    coq.ltac.call-ltac1 "cyp_split" G GL, premises GL.
  close (goal _ _ {{ _ \/ _ }} _ _ as G) :-
    coq.ltac.call-ltac1 "cyp_left" G GL, premises GL.
  close (goal _ _ {{ _ \/ _ }} _ _ as G) :-
    coq.ltac.call-ltac1 "cyp_right" G GL, premises GL.
  close (goal _ _ Ty _ _ as G) :- justify Ty Tac, run Tac G.

  pred run i:cyptac, i:goal.
  run (ltac N) G :- coq.ltac.call-ltac1 N G [].
  run (lemma T) G :- refine T G GL, premises GL.

  pred premises i:list sealed-goal.
  premises GL :- coq.ltac.all (coq.ltac.open close-tac) GL [].

  pred close-tac i:goal, o:list sealed-goal.
  close-tac G [] :- close G.

  % a step's goal: the rules, else the first default tactic that closes it
  pred close-step i:goal.
  close-step G :- close G, !.
  close-step G :- default-ltac N, coq.ltac.call-ltac1 N G [], !.

  % ---------------------------------------------------------------- %
  % Reading a step: its words and formulas, and their roles

  kind item type.
  type word string -> item.
  type formula term -> item.

  pred items i:term, o:list item.
  items (app [primitive (pstring P) | Args]) [word S | L] :- !,
    coq.pstring->string P S, args Args L.
  items (primitive (pstring P)) [word S] :- !, coq.pstring->string P S.
  items T [formula T].

  pred args i:list term, o:list item.
  args [] [].
  args [primitive (pstring P) | R] [word S | L] :- !,
    coq.pstring->string P S, args R L.
  args [T | R] [formula T | L] :- args R L.

  % the words of a text, in lower case, last one first
  pred words-rev i:string, o:list string.
  words-rev S W :-
    rex.split "[^A-Za-z'-]+" S W0,
    std.map W0 lower W1, std.rev W1 W.

  pred lower i:string, o:string.
  lower S L :-
    std.fold ["A","B","C","D","E","F","G","H","I","J","K","L","M","N","O",
              "P","Q","R","S","T","U","V","W","X","Y","Z"] S
      (u\ s\ s'\ sigma l\ lower-letter u l, rex.replace u l s s') L.

  pred lower-letter i:string, o:string.
  lower-letter "A" "a". lower-letter "B" "b". lower-letter "C" "c".
  lower-letter "D" "d". lower-letter "E" "e". lower-letter "F" "f".
  lower-letter "G" "g". lower-letter "H" "h". lower-letter "I" "i".
  lower-letter "J" "j". lower-letter "K" "k". lower-letter "L" "l".
  lower-letter "M" "m". lower-letter "N" "n". lower-letter "O" "o".
  lower-letter "P" "p". lower-letter "Q" "q". lower-letter "R" "r".
  lower-letter "S" "s". lower-letter "T" "t". lower-letter "U" "u".
  lower-letter "V" "v". lower-letter "W" "w". lower-letter "X" "x".
  lower-letter "Y" "y". lower-letter "Z" "z".

  % the role given by the last role word of a text, if any
  pred text-role i:string, o:role.
  text-role S R :- words-rev S W, std.mem W X, role-word X R, !.

  % the claims of a step: formulas whose role is claim and that are
  % propositions; the others are shown, not checked
  pred step-claims i:list item, i:role, o:list term.
  step-claims [] _ [].
  step-claims [word S | L] R C :- !,
    (text-role S R1, ! ; R1 = R), step-claims L R1 C.
  step-claims [formula F | L] claim [F | C] :- is-prop F, !, step-claims L claim C.
  step-claims [formula _ | L] R C :- step-claims L R C.

  pred is-prop i:term.
  is-prop F :- coq.elaborate-skeleton F Ty _ ok, coq.unify-eq Ty (sort prop) ok.

  pred backward i:list item.
  backward L :- std.mem L (word S), words-rev S W, std.mem W X, backward-word X, !.

  % the text of a step, to report it
  pred step-text i:list item, o:string.
  step-text L S :- std.map L item-text Ws, std.string.concat " " Ws S.
  pred item-text i:item, o:string.
  item-text (word S) S.
  item-text (formula F) S :-
    (coq.elaborate-skeleton F _ F1 ok, ! ; F1 = F),
    coq.term->string F1 S0, S is "`" ^ S0 ^ "`".

  pred conj i:list term, o:term.
  conj [C] C :- !.
  conj [C | L] {{ lp:C /\ lp:R }} :- conj L R.

  % ---------------------------------------------------------------- %
  % The proof skeleton: one hole per step

  % [prove Tac T P]: a proof P of T, in the current context, by the
  % step's tactic [some N] or else ([none]) by the rules and the default
  % tactics; if they fail, the premises of T are introduced and they are
  % tried again.  Fails if nothing closes the goal.
  pred prove i:option string, i:term, o:term.
  prove Tac T P :-
    coq.typecheck P T ok,
    coq.ltac.collect-goals P [SG] _,
    coq.ltac.open (solve-step Tac) SG [].

  pred solve-step i:option string, i:goal, o:list sealed-goal.
  solve-step Tac G [] :- try-close Tac G, !.
  solve-step Tac G [] :-
    coq.ltac.call-ltac1 "cyp_intros" G [SG], coq.ltac.open (solve-step Tac) SG [].

  pred try-close i:option string, i:goal.
  try-close none G :- close-step G.
  try-close (some N) G :- coq.ltac.call-ltac1 N G [].

  % [step-proof Tac Text T P Ko]: as [prove], reporting the step; a step
  % not proved leaves its hole open and is listed in Ko
  pred step-proof i:option string, i:string, i:term, o:term, o:list string.
  step-proof Tac Text T P [] :- prove Tac T P, !, coq.say "  ✅" Text.
  step-proof _ Text _ _ [Text] :- coq.say "  ❌" Text.

  % the justification of a step: a word "by name", name an Ltac tactic
  pred step-tac i:list item, o:option string.
  step-tac L (some N) :-
    std.mem L (word S), rex.match "^by [A-Za-z_0-9]+$" S, !,
    rex.replace "^by " "" S N.
  step-tac _ none.

  % [skel Steps Goal Skel Ko]: Skel proves Goal from the steps, in the
  % current context; Ko are the steps not proved.  A forward step proves
  % its claim C and adds it to the context (let c : C := P in ...); a
  % backward step proves C -> Goal, and the rest proves C.
  pred skel i:int, i:list term, i:term, o:term, o:list string.
  skel _ [] G P Ko :- step-proof none "the statement follows" G P Ko.
  skel K [S | Rest] G Skel Ko :-
    items S L, step-text L Text, step-tac L Tac,
    step-claims L claim Cs,
    if (Cs = []) (skel K Rest G Skel Ko)              % a comment
    (conj Cs C0,
     std.assert-ok! (coq.elaborate-ty-skeleton C0 _ C) "cyp: a claim does not type-check",
     if (backward L)
       (step-proof Tac Text (prod `_` C (_\ G)) P Ko1,
        Skel = app [P, SkelB],
        skel K Rest C SkelB Ko2,
        std.append Ko1 Ko2 Ko)
       % the claims are named c1, c2, ...: one name each
       (step-proof Tac Text C P Ko1,
        K1 is K + 1, Id is "c" ^ {std.any->string K1}, coq.id->name Id Nm,
        Skel = let Nm C P SkelF,
        (pi x\ decl x Nm C => skel K1 Rest G (SkelF x) Ko2),
        std.append Ko1 Ko2 Ko)).

  % the binders of the statement and of the body, in parallel
  pred lemma i:term, i:term, o:term, o:list string.
  lemma (prod N T A) (fun _ _ B) (fun N T S) Ko :- !,
    pi x\ decl x N T => lemma (A x) (B x) (S x) Ko.
  lemma G Body Skel Ko :- list-of Body Steps, skel 0 Steps G Skel Ko.

  pred list-of i:term, o:list term.
  list-of (app [global (indc Cons), _, X, R]) [X | L] :-
    coq.locate "cons" (indc Cons), !, list-of R L.
  list-of (app [global (indc Nil), _]) [] :- coq.locate "nil" (indc Nil), !.
  list-of T [T].

  % ---------------------------------------------------------------- %

  main [const-decl Name (some Body) Arity] :-
    coq.arity->term Arity Ty0,
    std.assert-ok! (coq.elaborate-ty-skeleton Ty0 _ Ty) "cyp: the statement does not type-check",
    coq.say "cyp:" Name,
    lemma Ty Body Proof Ko,
    if (Ko = [])
       (std.assert-ok! (coq.typecheck Proof Ty) "cyp: the proof does not type-check",
        coq.env.add-const Name Proof Ty @opaque! _, coq.say "cyp:" Name "proved")
       (std.length Ko N,
        coq.error "cyp:" N "step(s) of" Name "not proved").
}}.
Elpi Export Cyp.
