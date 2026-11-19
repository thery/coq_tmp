(* cyp: a proof written as text, checked node by node, inside Rocq.

   A text is the tree of the 2003 paper (prooftext/README.md, "The
   format"), and a verification condition generator: each node gives one
   condition, its conclusion, numbered like the node (2.1 the first
   subnode of node 2, 0 the top node, the statement).  cyp discharges
   them by the justifications and facts of the nodes, its rules and its
   default tactics.

     CypFile "proof.md".
       reads a cyp proof in Markdown, checks it, writes proof.checked.md
       and proof.cyp.json, and defines the lemma when every condition is
       discharged (used by the program cyp);

     Cyp File "proof.md".  Proof. tactics. CypQed.
     Cyp Lemma name binders : statement := [ step ; step ; ... ].
     Proof. tactics. CypQed.
       the same, but the conditions not discharged are the goals of the
       Proof block, in the order of the text; each goal is named after its
       node (?c2 for 2, ?c2_1 for 2.1), so that [c2]: tac. proves it.  In
       Cyp Lemma a step is a node: words (strings, with *X*{.just} for a
       justification), formulas (terms, each followed by its class,
       "{.claim}"), and its subnodes (a list of steps).

   What a proof means is in the Elpi files of elpi/: text.elpi (what cyp
   takes from the text of a node: its tags), check.elpi (closing a goal: the
   justifications, the facts, the rules), gaps.elpi (the gap tactic, a
   last try on a condition left open, cyp_gap of Gaps.v), proof.elpi (the
   proof of a statement from its tree), markdown.elpi (the checked Markdown
   and the JSON).  The tree is read by prooftext's reader
   (prooftext/tree.elpi, nodes.elpi).  The rules of a field are added to
   the database cyp.db (justify, justify_first, named). *)

From Stdlib Require Import PrimString List Lia Lra Ring Field.
From elpi Require Import elpi.
(* the coarse gap tactic cyp_gap, tried on a condition nothing else closes *)
From CypV Require Export Gaps.
(* itauto (coq-itauto): a reflexive SAT solver for propositional logic, run
   for the name tauto: tauto may run for minutes on goals that itauto closes
   at once.  With the flag Itauto Classic, itauto reasons classically when
   the classical axiom is loaded, as tauto does *)
From Cdcl Require Import Itauto.
#[export] Set Itauto Classic.

(* a claim C of the text, proved by p, is a hypothesis of the rest k *)
Definition cyp_have (C G : Prop) (p : C) (k : C -> G) : G := k p.

(* The tactics a proof may name in a justification *X*{.just} or in its
   header's by:, those of
   prooftext/tactics.elpi: the name N runs cyp_N, below.  More with
     Ltac my_tac := ...  Elpi Accumulate cyp.db lp:{{ tactic-name "my" "my_tac". }}. *)
Ltac cyp_lia := lia.            Ltac cyp_nia := nia.
Ltac cyp_lra := lra.            Ltac cyp_nra := nra.
Ltac cyp_ring := ring.          Ltac cyp_field := field.
Ltac cyp_tauto := itauto auto.        Ltac cyp_auto := auto.
Ltac cyp_easy := easy.          Ltac cyp_reflexivity := reflexivity.
Ltac cyp_assumption := assumption.   Ltac cyp_congruence := congruence.
(* firstorder, bounded (prooftext/Tactics.v, shared with xtext): firstorder has no bound (on a condition
   of xtext's half_le it ran over 30 s and took up to 7 GB) *)
Ltac cyp_firstorder := bounded_firstorder.
(* used by cyp itself *)
(* a hypothesis that is the goal, when the goal has no existential variable
   (on a premise of a lemma still to be found, a hypothesis would fix it) *)
Ltac cyp_hypothesis :=
  lazymatch goal with |- ?g => tryif has_evar g then fail else assumption end.
Ltac cyp_intros := progress intros.
(* the goal in weak head normal form, if that changes it *)
Ltac cyp_head_unfolded := progress hnf.
(* the goal has no existential variable *)
Ltac cyp_evar_free := match goal with |- ?g => tryif has_evar g then fail else idtac end.
Ltac cyp_eapply t := eapply t.
Ltac cyp_exact t := exact t.
(* an elimination principle t on the variable x: the goal abstracted over x
   first, so that the motive is that abstraction (as elim does) *)
Ltac cyp_elim_on t x := pattern x; eapply t.
Ltac cyp_split := split.
Ltac cyp_left := left.
Ltac cyp_right := right.
(* a name given by a justification, or the hypothesis a fact is, put first:
   a hypothesis moved last in the context (where tactics look first), a
   lemma added to it *)
Ltac cyp_first t :=
  first [ is_var t; move t at bottom | is_var t | let h := fresh "lem" in pose proof t as h ].

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
  % and the only ones tried when a node is justified by *Name*{.just}
  pred named o:string, o:term, o:cyptac.

  % [tactic-name Name Ltac]: a tactic that the rules of a proof add to
  % those of prooftext (elpi/check.elpi)
  pred tactic-name o:string, o:string.

  % [premise-depth-max N]: when a lemma is applied, its premises are
  % closed by the rules, which may apply lemmas in turn: at most N
  % lemmas deep (elpi/check.elpi).  A proof may change it with
  %   Elpi Accumulate cyp.db lp:{{ :before "premise-depth-max" premise-depth-max 8 :- !. }}.
  pred premise-depth-max o:int.
  :name "premise-depth-max"
  premise-depth-max 4.

  % the tactics tried when no rule closes a step, after the proof's own
  pred default-ltac o:string.
  default-ltac "cyp_tauto".
  default-ltac "cyp_lia".
  default-ltac "cyp_nia".
  default-ltac "cyp_lra".
}}.

(* the roles of the formulas, shared with xtext: lexicon/ (cyp reads no
   phrase of it: a formula has the role of its class) *)
From Lexicon Extra Dependency "lexicon.elpi" as lexicon.
(* the format of proof texts, shared with xtext: prooftext/ (the header and
   the document are loaded for checked.elpi, the marks of a checked text;
   names.elpi gives the names H1, H2, ... of unnamed hypotheses) *)
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "tree.elpi" as pt_tree.
From ProofText Extra Dependency "nodes.elpi" as pt_nodes.
From ProofText Extra Dependency "names.elpi" as pt_names.
From ProofText Extra Dependency "checked.elpi" as pt_checked.
From ProofText Extra Dependency "tactics.elpi" as pt_tactics.
From CypV Extra Dependency "elpi/text.elpi" as cyp_text.
From CypV Extra Dependency "elpi/check.elpi" as cyp_check.
From CypV Extra Dependency "elpi/gaps.elpi" as cyp_gaps.
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
Elpi Accumulate File lexicon.
Elpi Accumulate File pt_header pt_document pt_formulas pt_tree pt_nodes pt_names pt_checked pt_tactics.
Elpi Accumulate File cyp_text cyp_messages cyp_timing cyp_messages_en
  cyp_messages_fr cyp_messages_it cyp_gaps cyp_check cyp_proof cyp_markdown
  cyp_command.
Elpi Accumulate lp:{{
  % #[bare]: the conditions are printed, nothing is tried or defined
  main [str F] :- attributes A, std.mem A (attribute "bare" _), !,
    (proof-mode => bare-mode => check-file F Lang Name Ty Proof Rs),
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
Elpi Accumulate File lexicon.
Elpi Accumulate File pt_header pt_document pt_formulas pt_tree pt_nodes pt_names pt_checked pt_tactics.
Elpi Accumulate File cyp_text cyp_messages cyp_timing cyp_messages_en
  cyp_messages_fr cyp_messages_it cyp_gaps cyp_check cyp_proof cyp_markdown
  cyp_command.
Elpi Accumulate lp:{{
  % A step written in Rocq is a node of the tree, as a list item of a
  % Markdown text: its words are strings, read as the text of a node
  % (prooftext's text-parts: *X*{.just} is a justification); its formulas
  % are terms, and the string right after a term may give its class and
  % its name, "{.claim} (n)", as in a Markdown text (prooftext's
  % after-formula); a list among its arguments is the list of its
  % subnodes:
  %   "We have" (0 < b + a) "{.claim}, since" [ "From" (0 < a) "{.fact}" ... ]

  % [raw-node T N]: the node of the step T
  pred raw-node i:term, o:prooftext.node.
  raw-node T (prooftext.node prooftext.list-item prooftext.unplaced
      (prooftext.spot 0 0) (prooftext.spot 0 0) Cs) :-
    step-arguments T Args, raw-contents Args Cs.

  % [step-arguments T Args]: the words, formulas and lists of a step
  pred step-arguments i:term, o:list term.
  step-arguments (app [primitive (pstring P) | As]) [primitive (pstring P) | As] :- !.
  step-arguments T [T].

  % [raw-contents Args Cs]: the contents of a node of these arguments
  pred raw-contents i:list term, o:list prooftext.content.
  raw-contents [] [].
  raw-contents [primitive (pstring P) | R] [prooftext.run S Ps | Cs] :- !,
    coq.pstring->string P S, prooftext.text-parts S Ps, raw-contents R Cs.
  raw-contents [L | R] Cs :- is-list L, !,
    list-of L Ts, std.map Ts raw-node Ns, std.map Ns (n\ c\ c = prooftext.sub n) Subs,
    raw-contents R Cs1, std.append Subs Cs1 Cs.
  raw-contents [T, primitive (pstring P) | R] [prooftext.run S Ps | Cs] :- !,
    coq.pstring->string P S, prooftext.after-formula S C N S1,
    prooftext.text-parts S1 Ps1, raw-contents R Cs,
    Ps = [prooftext.term-part C T N | Ps1].
  raw-contents [T | R] [prooftext.run "" [prooftext.term-part "" T none] | Cs] :-
    raw-contents R Cs.

  % [is-list T]: T is a Rocq list, written [ ... ; ... ]
  pred is-list i:term.
  is-list (app [global (indc K) | _]) :-
    (coq.locate "cons" (indc K) ; coq.locate "nil" (indc K)), !.

  % [list-of T Ts]: the Rocq list T as an Elpi list (a term that is not a
  % list: itself, alone)
  pred list-of i:term, o:list term.
  list-of (app [global (indc Cons), _, X, R]) [X | L] :-
    coq.locate "cons" (indc Cons), !, list-of R L.
  list-of (app [global (indc Nil), _]) [] :- coq.locate "nil" (indc Nil), !.
  list-of T [T].

  % [lemma Ty Body P Rs]: the binders of the statement and of the body, in
  % parallel; then the top node: the conclusion of the statement, the
  % steps of the body as its subnodes
  pred lemma i:term, i:term, o:term, o:list report.
  lemma (prod N T A) (fun _ _ B) (fun N T S) Rs :- !,
    under-decl N T (x\ lemma (A x) (B x) (S x) Rs).
  lemma G Body P Rs :-
    list-of Body Ts, std.map Ts raw-node Ns, std.map Ns (n\ c\ c = prooftext.sub n) Subs,
    Top = prooftext.node prooftext.whole-text prooftext.unplaced (prooftext.spot 0 0) (prooftext.spot 0 0)
      [prooftext.run "" [prooftext.term-part "claim" G none] | Subs],
    check-tree Top _ P Rs.

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

  % the language of Cyp Lemma: #[lang="fr"], else prooftext's default (English)
  pred lemma-lang o:string.
  lemma-lang L :- attributes A, std.mem A (attribute "lang" (leaf-str L)), !.
  lemma-lang L :- prooftext.default-lang L.

  % the data for CypQed: the name, the language and the statement
  main-interp-proof [const-decl Name (some Body) Arity] _ Proof GL (qed-data Name Lang Ty) :-
    lemma-lang Lang,
    (current-lang Lang :- !) => (
      coq.arity->term Arity Ty0,
      std.assert-ok! (coq.elaborate-ty-skeleton Ty0 _ Ty) {msg "statement-no-typecheck" []},
      coq.say "cyp:" Name,
      ((current-scope "" :- !) => proof-mode => with-attributes (lemma Ty Body Proof Rs)),
      std.forall Rs (r\ sigma I S\ r = rep I S,
        (S = ok, coq.say "  ✅" I ; S = todo _, true ; coq.say "  ❌" I S)),
      open Name Ty Proof Rs GL).
  main-interp-proof [str "File", str F] _ Proof GL (qed-data Name Lang Ty) :-
    (proof-mode => with-attributes (check-file F Lang Name Ty Proof Rs)),
    (current-lang Lang :- !) => open Name Ty Proof Rs GL.
}}.
#[proof="begin"] Elpi Export Cyp.

(* the end of the Proof block of Cyp File or Cyp Lemma *)
Elpi Command CypQed.
Elpi Accumulate File lexicon.
Elpi Accumulate File pt_header pt_document pt_formulas pt_tree pt_nodes pt_names pt_checked pt_tactics.
Elpi Accumulate File cyp_text cyp_messages cyp_timing cyp_messages_en
  cyp_messages_fr cyp_messages_it cyp_gaps cyp_check cyp_proof cyp_markdown
  cyp_command.
Elpi Accumulate lp:{{
  main-interp-qed _ _ Proof _ (qed-data Name Lang Ty) :-
    (current-lang Lang :- !) => (
      define Name Ty Proof,
      say "proved-lemma" [Name]).
}}.
#[proof="end"] Elpi Export CypQed.
