(* cyp: a proof written as text, checked step by step, inside Rocq.

     Elpi CypFile "proof.md".
       reads a cyp proof in Markdown, checks it, writes proof.checked.md
       and proof.cyp.json, and defines the lemma when every step is proved;

     Cyp Lemma name binders : statement := [ step ; step ; ... ].
       the same with the steps written in Rocq: a step is words (strings)
       and formulas (terms), "by X" for its justification.

   What a proof means is in the Elpi files of elpi/: text.elpi (words,
   formulas and their roles), vocab_*.elpi (the vocabulary of each
   language), check.elpi (closing a goal), proof.elpi (the proof of a
   statement from its steps), markdown.elpi (the Markdown).  The rules of a
   field are added to the database cyp.db (justify, justify_first, named). *)

From Stdlib Require Import PrimString List Lia Lra Ring Field.
From elpi Require Import elpi.

(* The tactics a proof may name in *by X* or in its header's by:, and the
   default tactics.  More with
     Ltac my_tac := ...  Elpi Accumulate cyp.db lp:{{ tactic-name "my" "my_tac". }}. *)
Ltac cyp_lia := lia.            Ltac cyp_nia := nia.
Ltac cyp_lra := lra.            Ltac cyp_nra := nra.
Ltac cyp_ring := ring.          Ltac cyp_field := field.
Ltac cyp_tauto := tauto.        Ltac cyp_auto := auto.
Ltac cyp_easy := easy.          Ltac cyp_reflexivity := reflexivity.
Ltac cyp_assumption := assumption.
(* used by cyp itself *)
Ltac cyp_intros := progress intros.
Ltac cyp_eapply t := eapply t.
Ltac cyp_split := split.
Ltac cyp_left := left.
Ltac cyp_right := right.

Elpi Db cyp.db lp:{{
  % the tactics of a rule: [ltac N] the Ltac tactic N, which must close the
  % goal; [apply T] the lemma T, its arguments found by unification, its
  % premises closed by the rules or the default tactics; [lemma T] the
  % same with an explicit term T (holes _)
  kind cyptac type.
  type ltac string -> cyptac.
  type apply term -> cyptac.
  type lemma term -> cyptac.

  % [justify Pattern Tac]: on a goal that matches Pattern, try Tac
  pred justify i:term, o:cyptac.
  % [justify_first Pattern Tac]: the same, tried before every [justify]
  pred justify_first i:term, o:cyptac.
  % [named Name Pattern Tac]: a rule with a name, tried like the others,
  % and the only ones tried when a step says *by Name*
  pred named o:string, o:term, o:cyptac.

  % [tactic-name Name Ltac]: a tactic a proof may name
  pred tactic-name o:string, o:string.
  tactic-name "lia" "cyp_lia".        tactic-name "nia" "cyp_nia".
  tactic-name "lra" "cyp_lra".        tactic-name "nra" "cyp_nra".
  tactic-name "ring" "cyp_ring".      tactic-name "field" "cyp_field".
  tactic-name "tauto" "cyp_tauto".    tactic-name "auto" "cyp_auto".
  tactic-name "easy" "cyp_easy".      tactic-name "reflexivity" "cyp_reflexivity".
  tactic-name "assumption" "cyp_assumption".

  % the tactics tried when no rule closes a step, after the proof's own
  pred default-ltac o:string.
  default-ltac "cyp_tauto".
  default-ltac "cyp_lia".
  default-ltac "cyp_nia".
  default-ltac "cyp_lra".
}}.

From CypV Extra Dependency "elpi/text.elpi" as cyp_text.
From CypV Extra Dependency "elpi/vocab_en.elpi" as cyp_vocab_en.
From CypV Extra Dependency "elpi/vocab_fr.elpi" as cyp_vocab_fr.
From CypV Extra Dependency "elpi/vocab_it.elpi" as cyp_vocab_it.
From CypV Extra Dependency "elpi/check.elpi" as cyp_check.
From CypV Extra Dependency "elpi/proof.elpi" as cyp_proof.
From CypV Extra Dependency "elpi/markdown.elpi" as cyp_markdown.

(* ------------------------------------------------------------------ *)

Elpi Command CypFile.
Elpi Accumulate Db cyp.db.
Elpi Accumulate File cyp_text.
Elpi Accumulate File cyp_vocab_en.
Elpi Accumulate File cyp_vocab_fr.
Elpi Accumulate File cyp_vocab_it.
Elpi Accumulate File cyp_check.
Elpi Accumulate File cyp_proof.
Elpi Accumulate File cyp_markdown.
Elpi Accumulate lp:{{
  % the default tactics of the header's by: field, e.g. "lra | assumption"
  pred by-clauses i:string, o:list prop.
  by-clauses "" [] :- !.
  by-clauses S Cl :- rex.split " *| *" S Ns, std.map Ns by-clause Cl.
  pred by-clause i:string, o:prop.
  by-clause N (proof-default T) :- trim N T.

  main [str F] :-
    rex.replace "[.]md$" ".checked.md" F OutMd,
    rex.replace "[.]md$" ".cyp.json" F OutJs,
    read-proof F H Name Stmt SF SL Ns,
    field H "scope" Sc, field H "by" By, field H "lang" Lang0,
    (Lang0 = "", Lang = "en" ; Lang = Lang0), !,
    by-clauses By Cl,
    coq.say "cyp:" Name,
    (current-lang Lang :- !) => (current-scope Sc :- !) => Cl => (
      justification Stmt _ Stmt1, pieces Stmt1 P, elements P rclaim SEs,
      binders SEs Vs, hyps SEs Hs, claims SEs Gs,
      steps-of 1 Ns _ Steps,
      statement Vs Hs Gs Steps Ty Proof Rs,
      write-md OutMd H Name Stmt Ns Rs,
      write-json OutJs SF SL SEs Ns Rs),
    std.filter Rs (r\ sigma I S\ r = rep I S, not (S = ok)) Ko,
    std.length Rs NR, std.length Ko NK, NP is NR - NK,
    if (Ko = [])
       (std.assert-ok! (coq.typecheck Proof Ty) "cyp: the proof does not type-check",
        coq.env.add-const Name Proof Ty @opaque! _,
        coq.say "cyp:" Name "proved," NP "steps")
       (Msg is "cyp: " ^ {std.any->string NK} ^ " of " ^ {std.any->string NR} ^ " steps of " ^ Name ^ " not proved, see " ^ OutMd, coq.error Msg).
}}.

(* ------------------------------------------------------------------ *)

#[arguments(raw)] Elpi Command Cyp.
Elpi Accumulate Db cyp.db.
Elpi Accumulate File cyp_text.
Elpi Accumulate File cyp_vocab_en.
Elpi Accumulate File cyp_check.
Elpi Accumulate File cyp_proof.
Elpi Accumulate lp:{{
  % a step written in Rocq: words (primitive strings) and terms
  pred raw-step i:int, i:term, o:step.
  raw-step I T (step I Es Tac []) :-
    raw-items T Is, raw-elements Is rclaim Es0,
    (std.mem Es0 (txt W), rex.match "^by " W, !,
     rex.replace "^by +" "" W X, Tac = some X,
     std.filter Es0 (e\ not (e = txt W)) Es ; Tac = none, Es = Es0).

  kind ritem type.
  type rword string -> ritem.
  type rterm term -> ritem.

  pred raw-items i:term, o:list ritem.
  raw-items (app [primitive (pstring P) | As]) [rword S | L] :- !,
    coq.pstring->string P S, raw-args As L.
  raw-items (primitive (pstring P)) [rword S] :- !, coq.pstring->string P S.
  raw-items T [rterm T].
  pred raw-args i:list term, o:list ritem.
  raw-args [] [].
  raw-args [primitive (pstring P) | R] [rword S | L] :- !,
    coq.pstring->string P S, raw-args R L.
  raw-args [T | R] [rterm T | L] :- raw-args R L.

  pred raw-elements i:list ritem, i:role, o:list element.
  raw-elements [] _ [].
  raw-elements [rword W | L] R [txt W | E] :-
    (text-role W R1, ! ; R1 = R), raw-elements L R1 E.
  raw-elements [rterm T | L] R [eltt R T | E] :- raw-elements L R E.

  pred list-of i:term, o:list term.
  list-of (app [global (indc Cons), _, X, R]) [X | L] :-
    coq.locate "cons" (indc Cons), !, list-of R L.
  list-of (app [global (indc Nil), _]) [] :- coq.locate "nil" (indc Nil), !.
  list-of T [T].

  pred numbered i:int, i:list term, o:list step.
  numbered _ [] [].
  numbered I [T | L] [S | Ss] :- raw-step I T S, I1 is I + 1, numbered I1 L Ss.

  % the binders of the statement and of the body, in parallel
  pred lemma i:term, i:term, o:term, o:list report.
  lemma (prod N T A) (fun _ _ B) (fun N T S) Rs :- !,
    pi x\ decl x N T => lemma (A x) (B x) (S x) Rs.
  lemma G Body P Rs :-
    list-of Body Ts, numbered 1 Ts Steps, level 0 0 none Steps G P Rs.

  main [const-decl Name (some Body) Arity] :-
    coq.arity->term Arity Ty0,
    std.assert-ok! (coq.elaborate-ty-skeleton Ty0 _ Ty) "cyp: the statement does not type-check",
    coq.say "cyp:" Name,
    (current-lang "en" :- !) => (current-scope "" :- !) => lemma Ty Body Proof Rs,
    std.forall Rs (r\ sigma I S\ r = rep I S, (S = ok, coq.say "  ✅ step" I ; coq.say "  ❌ step" I S)),
    std.filter Rs (r\ sigma I S\ r = rep I S, not (S = ok)) Ko,
    if (Ko = [])
       (std.assert-ok! (coq.typecheck Proof Ty) "cyp: the proof does not type-check",
        coq.env.add-const Name Proof Ty @opaque! _, coq.say "cyp:" Name "proved")
       (std.length Ko N, coq.error "cyp:" N "step(s) of" Name "not proved").
}}.
Elpi Export Cyp.
