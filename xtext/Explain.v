(* The command [Explain foo.]: print the proof of [foo] as text, after the
   basic transducer of "Extracting Text from Proofs" (TLCA 1995).
   [Explain foo to "foo.md".] writes the text to the file foo.md.
   [Explain foo to "foo.md" in "fr".]: the same in French (the languages of
   the lexicon: en, fr, it, de, nl, ru, zh, ar, ko, la
   [Explain_partial.], inside a proof, prints the proof so far. *)
From Stdlib Require Import Lia.
From elpi Require Import elpi.
(* xtext's writer, in elpi/: the structure of texts, printing, words,
   formulas that type-check again, kinds of binders, inductive types, the
   transducer and its forms (abstractions, applications, inductive
   constructions), the document *)
From XText Extra Dependency "elpi/text-tree.elpi" as xt_text_tree.
From XText Extra Dependency "elpi/printing.elpi" as xt_printing.
From XText Extra Dependency "elpi/words.elpi" as xt_words.
From XText Extra Dependency "elpi/reparse.elpi" as xt_reparse.
From XText Extra Dependency "elpi/kinds.elpi" as xt_kinds.
From XText Extra Dependency "elpi/inductive.elpi" as xt_inductive.
From XText Extra Dependency "elpi/declarations.elpi" as xt_declarations.
From XText Extra Dependency "elpi/transducer.elpi" as xt_transducer.
From XText Extra Dependency "elpi/abstractions.elpi" as xt_abstractions.
From XText Extra Dependency "elpi/applications.elpi" as xt_applications.
From XText Extra Dependency "elpi/inductive-text.elpi" as xt_inductive_text.
From XText Extra Dependency "elpi/document.elpi" as xt_document.
(* the lexicon (../lexicon): the roles and the phrases of each language,
   shared with the reader cyp *)
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From Lexicon Extra Dependency "lang_en.elpi" as lex_en.
From Lexicon Extra Dependency "lang_fr.elpi" as lex_fr.
From Lexicon Extra Dependency "lang_it.elpi" as lex_it.
From Lexicon Extra Dependency "lang_de.elpi" as lex_de.
From Lexicon Extra Dependency "lang_nl.elpi" as lex_nl.
From Lexicon Extra Dependency "lang_ru.elpi" as lex_ru.
From Lexicon Extra Dependency "lang_zh.elpi" as lex_zh.
From Lexicon Extra Dependency "lang_ar.elpi" as lex_ar.
From Lexicon Extra Dependency "lang_ko.elpi" as lex_ko.
From Lexicon Extra Dependency "lang_la.elpi" as lex_la.
From XText Extra Dependency "elpi/annotation.elpi" as types.
From XText Extra Dependency "elpi/sentences.elpi" as sentences.
From XText Extra Dependency "elpi/staged.elpi" as staged.

(* The tactics tried on long subproofs (see xtext-tactic below).  Each is
   an Ltac definition (rocq-elpi calls Ltac definitions by name), with a
   time limit. *)
Ltac xtext_tauto := timeout 2 tauto.
Ltac xtext_lia := timeout 2 lia.
(* the tactics that check a contraction (those of cyp's default "by") *)
Ltac xtext_g_tauto := timeout 1 tauto.
Ltac xtext_g_congruence := timeout 1 congruence.
Ltac xtext_g_lia := timeout 1 lia.
Ltac xtext_g_firstorder := timeout 1 firstorder.
Ltac xtext_g_auto := timeout 1 auto.

Elpi Db xtext.db lp:{{
  % [xtext-tactic Ltac Text]: the Ltac definition Ltac is tried on a long
  % subproof; if it closes it, the step reads "We have P *by Text*".
  % Add yours with: Elpi Accumulate xtext.db lp:{{ xtext-tactic "my_lra" "lra". }}.
  pred xtext-tactic o:string, o:string.
  xtext-tactic "xtext_tauto" "tauto".
  xtext-tactic "xtext_lia" "lia".
  % [xtext-threshold N]: the tactics are tried on a proper subproof whose
  % proof term has at least N nodes.  Change it with
  % Elpi Accumulate xtext.db lp:{{ :before "xtext-threshold" xtext-threshold 50 :- !. }}.
  pred xtext-threshold o:int.
  :name "xtext-threshold"
  xtext-threshold 300.
  % [xtext-contraction S]: the contraction of application steps (thesis
  % 3.4.2): "none", "guarded" (default) or "maximal".  The variable
  % XTEXT_CONTRACTION overrides it.
  pred xtext-contraction o:string.
  :name "xtext-contraction"
  xtext-contraction "guarded".
  % [xtext-guard-tactic Ltac Text]: the tactics that check a guarded
  % contraction (the step must still follow from its premises); the one
  % that succeeds becomes the step's justification, *by Text*.
  pred xtext-guard-tactic o:string, o:string.
  xtext-guard-tactic "xtext_g_tauto" "tauto".
  xtext-guard-tactic "xtext_g_congruence" "congruence".
  xtext-guard-tactic "xtext_g_lia" "lia".
  xtext-guard-tactic "xtext_g_firstorder" "firstorder".
  xtext-guard-tactic "xtext_g_auto" "auto".
  % [xtext-lang L]: the language of the texts ("en", "fr", "it"), whose
  % phrases are those of the lexicon's lang_L.elpi.  The variable XTEXT_LANG
  % overrides it.
  pred xtext-lang o:string.
  :name "xtext-lang"
  xtext-lang "en".
  % [xtext-annotation S]: the type expressions written (thesis chapter 3):
  % "all" (default, the texts of the earlier rounds) or "double" (the double
  % annotation of 3.3.4, Fig. 3.9; types.elpi).  The variable
  % XTEXT_ANNOTATION overrides it.
  pred xtext-annotation o:string.
  :name "xtext-annotation"
  xtext-annotation "all".
  % [xtext-translation S]: how a proof becomes text: "direct" (default,
  % term to text in one walk, xtext.elpi) or "staged" (annotation, then
  % contraction, then writing, as in Coscoy's thesis; staged.elpi; the
  % contraction strategy is xtext-contraction).  The variable
  % XTEXT_TRANSLATION overrides it.
  pred xtext-translation o:string.
  :name "xtext-translation"
  xtext-translation "direct".
}}.

Elpi Command Explain.
Elpi Accumulate Db xtext.db.
Elpi Accumulate File lex_core.
Elpi Accumulate File lex_en.
Elpi Accumulate File lex_fr.
Elpi Accumulate File lex_it.
Elpi Accumulate File lex_de.
Elpi Accumulate File lex_nl.
Elpi Accumulate File lex_ru.
Elpi Accumulate File lex_zh.
Elpi Accumulate File lex_ar.
Elpi Accumulate File lex_ko.
Elpi Accumulate File lex_la.
Elpi Accumulate File types.
Elpi Accumulate File xt_text_tree.
Elpi Accumulate File xt_printing.
Elpi Accumulate File xt_words.
Elpi Accumulate File xt_reparse.
Elpi Accumulate File xt_kinds.
Elpi Accumulate File xt_inductive.
Elpi Accumulate File xt_declarations.
Elpi Accumulate File xt_transducer.
Elpi Accumulate File xt_abstractions.
Elpi Accumulate File xt_applications.
Elpi Accumulate File xt_inductive_text.
Elpi Accumulate File xt_document.
Elpi Accumulate File sentences.
Elpi Accumulate File staged.
Elpi Accumulate lp:{{
  main [str N] :- !, explain N T, coq.say T.
  main [str N, str "in", str L] :- !, ((writer-lang L :- !) => explain N T), coq.say T.
  main [str N, str "to", str F] :- !, explain N T, write-text F T.
  main [str N, str "to", str F, str "in", str L] :- !,
    ((writer-lang L :- !) => explain N T), write-text F T.
  main _ :- coq.error "usage: Explain name [to \"file.md\"] [in \"lang\"].".
  pred write-text i:string, i:string.
  write-text F T :- open_out F O, output O T, close_out O, coq.say "Explain: written" F.
}}.
Elpi Export Explain.

(* [Explain_partial.] inside a proof: prints the text of the proof so far,
   each open goal written "Prove G" at its place.  It ends the proof (as
   Abort does): rocq-elpi gives the partial proof only to a command that
   closes the proof. *)
Elpi Command Explain_partial.
Elpi Accumulate Db xtext.db.
Elpi Accumulate File lex_core.
Elpi Accumulate File lex_en.
Elpi Accumulate File lex_fr.
Elpi Accumulate File lex_it.
Elpi Accumulate File lex_de.
Elpi Accumulate File lex_nl.
Elpi Accumulate File lex_ru.
Elpi Accumulate File lex_zh.
Elpi Accumulate File lex_ar.
Elpi Accumulate File lex_ko.
Elpi Accumulate File lex_la.
Elpi Accumulate File types.
Elpi Accumulate File xt_text_tree.
Elpi Accumulate File xt_printing.
Elpi Accumulate File xt_words.
Elpi Accumulate File xt_reparse.
Elpi Accumulate File xt_kinds.
Elpi Accumulate File xt_inductive.
Elpi Accumulate File xt_declarations.
Elpi Accumulate File xt_transducer.
Elpi Accumulate File xt_abstractions.
Elpi Accumulate File xt_applications.
Elpi Accumulate File xt_inductive_text.
Elpi Accumulate File xt_document.
Elpi Accumulate File sentences.
Elpi Accumulate File staged.
Elpi Accumulate lp:{{
  main-interp-qed [str "to", str F] _ P _ Name :- !,
    (if (var Name) (N = "proof") (N = Name)),
    explain-partial N P T, open_out F O, output O T, close_out O,
    coq.say "Explain_partial: written" F.
  main-interp-qed _ _ P _ Name :-
    (if (var Name) (N = "proof") (N = Name)),
    explain-partial N P T, coq.say T.
}}.
#[proof="end"]
Elpi Export Explain_partial.
