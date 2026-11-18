(* cyp: a proof written as text, checked step by step, inside Rocq.

   A text is a verification condition generator: each step gives
   conditions, numbered after the step (2.1 the first sub-step of step 2,
   2a and 2b the two claims of step 2, 0 the statement after the steps).
   cyp discharges them by its rules and default tactics.

     CypFile "proof.md".
       reads a cyp proof in Markdown, checks it, writes proof.checked.md
       and proof.cyp.json, and defines the lemma when every condition is
       discharged (used by the program cyp);

     Cyp File "proof.md".  Proof. tactics. CypQed.
     Cyp Lemma name binders : statement := [ step ; step ; ... ].
     Proof. tactics. CypQed.
       the same, but the conditions not discharged are the goals of the
       Proof block, in the order of the text; each goal says its number
       (condition := cyp_condition "2a").  In Cyp Lemma a step is words (strings) and
       formulas (terms), "by X" for its justification.

   What a proof means is in the Elpi files of elpi/: text.elpi (words,
   formulas and their roles), vocab_*.elpi (the vocabulary of each
   language), check.elpi (closing a goal), proof.elpi (the proof of a
   statement from its steps), markdown.elpi (the Markdown).  The rules of a
   field are added to the database cyp.db (justify, justify_first, named). *)

From Stdlib Require Import PrimString List Lia Lra Ring Field.
From elpi Require Import elpi.

(* a claim C of the text, proved by p, is a hypothesis of the rest k *)
Definition cyp_have (C G : Prop) (p : C) (k : C -> G) : G := k p.

(* the label of a goal of the Proof block: condition := cyp_condition "2a";
   removed from the proof before the lemma is defined *)
Definition cyp_condition (number : PrimString.string) : unit := tt.

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
From CypV Extra Dependency "elpi/command.elpi" as cyp_command.
From CypV Extra Dependency "elpi/messages.elpi" as cyp_messages.
From CypV Extra Dependency "elpi/timing.elpi" as cyp_timing.
From CypV Extra Dependency "elpi/messages_en.elpi" as cyp_messages_en.
From CypV Extra Dependency "elpi/messages_fr.elpi" as cyp_messages_fr.
From CypV Extra Dependency "elpi/messages_it.elpi" as cyp_messages_it.

(* ------------------------------------------------------------------ *)

Elpi Command CypFile.
Elpi Accumulate Db cyp.db.
Elpi Accumulate File cyp_text.
Elpi Accumulate File cyp_messages.
Elpi Accumulate File cyp_timing.
Elpi Accumulate File cyp_messages_en.
Elpi Accumulate File cyp_messages_fr.
Elpi Accumulate File cyp_messages_it.
Elpi Accumulate File cyp_vocab_en.
Elpi Accumulate File cyp_vocab_fr.
Elpi Accumulate File cyp_vocab_it.
Elpi Accumulate File cyp_check.
Elpi Accumulate File cyp_proof.
Elpi Accumulate File cyp_markdown.
Elpi Accumulate File cyp_command.
Elpi Accumulate lp:{{
  % #[bare]: the conditions are printed, nothing is tried or defined
  main [str F] :- attributes A, std.mem A (attribute "bare" _), !,
    proof-mode => bare-mode => check-file F Lang Name Ty Proof Rs,
    (current-lang Lang :- !) => (
      std.assert-ok! (coq.typecheck Proof Ty) {msg "no-typecheck" []},
      coq.ltac.collect-goals Proof GL _, say-goals GL,
      count Rs Steps _ Todo, std.length Steps NS, std.length Todo NT,
      say "conditions" [Name, {std.any->string NS}, {std.any->string NT}]).
  main [str F] :-
    check-file F Lang Name Ty Proof Rs,
    count Rs Steps Ko _,
    std.length Steps NR, std.length Ko NK, NP is NR - NK,
    (current-lang Lang :- !) => (
    if (Ko = [])
       (define Name Ty Proof, say "proved" [Name, {std.any->string NP}])
       (rex.replace "[.]md$" ".checked.md" F OutMd,
        std.string.concat ", " Ko KoS,
        coq.error {msg "not-proved" [{std.any->string NK}, {std.any->string NR}, Name, KoS, OutMd]})).
}}.
Elpi Export CypFile.

(* ------------------------------------------------------------------ *)

#[arguments(raw)] Elpi Command Cyp.
Elpi Accumulate Db cyp.db.
Elpi Accumulate File cyp_text.
Elpi Accumulate File cyp_messages.
Elpi Accumulate File cyp_timing.
Elpi Accumulate File cyp_messages_en.
Elpi Accumulate File cyp_messages_fr.
Elpi Accumulate File cyp_messages_it.
Elpi Accumulate File cyp_vocab_en.
Elpi Accumulate File cyp_vocab_fr.
Elpi Accumulate File cyp_vocab_it.
Elpi Accumulate File cyp_check.
Elpi Accumulate File cyp_proof.
Elpi Accumulate File cyp_markdown.
Elpi Accumulate File cyp_command.
Elpi Accumulate lp:{{
  % a step written in Rocq: words (primitive strings) and terms
  pred raw-step i:string, i:term, o:step.
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
  numbered I [T | L] [S | Ss] :-
    raw-step {std.any->string I} T S, I1 is I + 1, numbered I1 L Ss.

  % the binders of the statement and of the body, in parallel
  pred lemma i:term, i:term, o:term, o:list report.
  lemma (prod N T A) (fun _ _ B) (fun N T S) Rs :- !,
    pi x\ decl x N T => lemma (A x) (B x) (S x) Rs.
  lemma G Body P Rs :-
    list-of Body Ts, numbered 1 Ts Steps, level "0" none Steps G P Rs.

  % the proof is opened with the conditions left as its goals
  pred open i:string, i:term, i:term, i:list report, o:list sealed-goal.
  open Name Ty Proof Rs GL :-
    count Rs Steps Ko Todo,
    if (Ko = []) true
       (std.string.concat ", " Ko KoS, coq.error {msg "steps-not-parsed" [Name, KoS]}),
    std.assert-ok! (coq.typecheck Proof Ty) {msg "no-typecheck" []},
    coq.ltac.collect-goals Proof GL _,
    std.length Steps NS, std.length Todo NT,
    if (Todo = [])
       (say "all-discharged" [Name, {std.any->string NS}])
       (std.string.concat ", " Todo TS,
        say "left" [Name, {std.any->string NS}, {std.any->string NT}, TS],
        say-todo Rs).

  % the language of Cyp Lemma: #[lang="fr"], English by default
  pred lemma-lang o:string.
  lemma-lang L :- attributes A, std.mem A (attribute "lang" (leaf-str L)), !.
  lemma-lang "en".

  % the data for CypQed: the name, the language and the statement
  main-interp-proof [const-decl Name (some Body) Arity] _ Proof GL (qed-data Name Lang Ty) :-
    lemma-lang Lang,
    (current-lang Lang :- !) => (
      coq.arity->term Arity Ty0,
      std.assert-ok! (coq.elaborate-ty-skeleton Ty0 _ Ty) {msg "statement-no-typecheck" []},
      coq.say "cyp:" Name,
      (current-scope "" :- !) => proof-mode => with-attributes (lemma Ty Body Proof Rs),
      std.forall Rs (r\ sigma I S\ r = rep I S,
        (S = ok, coq.say "  ✅" I ; S = todo _, true ; coq.say "  ❌" I S)),
      open Name Ty Proof Rs GL).
  main-interp-proof [str "File", str F] _ Proof GL (qed-data Name Lang Ty) :-
    proof-mode => with-attributes (check-file F Lang Name Ty Proof Rs),
    (current-lang Lang :- !) => open Name Ty Proof Rs GL.
}}.
#[proof="begin"] Elpi Export Cyp.

(* the end of the Proof block of Cyp File or Cyp Lemma *)
Elpi Command CypQed.
Elpi Accumulate File cyp_text.
Elpi Accumulate File cyp_messages.
Elpi Accumulate File cyp_timing.
Elpi Accumulate File cyp_messages_en.
Elpi Accumulate File cyp_messages_fr.
Elpi Accumulate File cyp_messages_it.
Elpi Accumulate File cyp_command.
Elpi Accumulate lp:{{
  main-interp-qed _ _ Proof _ (qed-data Name Lang Ty) :-
    (current-lang Lang :- !) => (
      remove-labels Proof Proof1,
      define Name Ty Proof1,
      say "proved-lemma" [Name]).
}}.
#[proof="end"] Elpi Export CypQed.
