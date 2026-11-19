(* The command [Typst "proof.md" to "proof.typ".]: the Typst source of a
   proof text (written by xtext, or checked by cyp), for its PDF.  It reads
   the Markdown with prooftext's reader (tree.elpi, read-document) and writes it with
   write-typst-in (typst.elpi); pdf.sh runs it, then typst.

   The formulas are mathematics (maths.elpi), or Rocq code with the option
   [as code]:
     Typst "proof.md" to "proof.typ".            (* mathematics *)
     Typst "proof.md" to "proof.typ" as code.    (* Rocq code *)
   For mathematics, the formulas are elaborated in the current Rocq
   context: the libraries of the text (its header's require line) must be
   loaded before the command (pdf.sh does it).  The command says how many
   formulas it could not elaborate (they are shown as code).
   rocq c -Q ../lexicon Lexicon -Q . ProofText Typst.v *)
From elpi Require Import elpi.
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
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "tree.elpi" as pt_tree.
From ProofText Extra Dependency "checked.elpi" as pt_checked.
From ProofText Extra Dependency "maths-table.elpi" as pt_maths_table.
From ProofText Extra Dependency "maths.elpi" as pt_maths.
From ProofText Extra Dependency "maths-typst.elpi" as pt_maths_typst.
From ProofText Extra Dependency "links.elpi" as pt_links.
From ProofText Extra Dependency "typst.elpi" as pt_typst.

Elpi Command Typst.
Elpi Accumulate File lex_core lex_en lex_fr lex_it lex_de lex_nl lex_ru lex_zh
  lex_ar lex_ko lex_la pt_header pt_document pt_formulas pt_tree pt_checked
  pt_maths_table pt_maths pt_maths_typst pt_links pt_typst.
Elpi Accumulate lp:{{
  main [str In, str "to", str Out] :- !, typst-of In Out prooftext.maths.
  main [str In, str "to", str Out, str "as", str "maths"] :- !, typst-of In Out prooftext.maths.
  main [str In, str "to", str Out, str "as", str "code"] :- !, typst-of In Out prooftext.code.
  main _ :- coq.error "usage: Typst \"proof.md\" to \"proof.typ\" [as maths | as code].".

  % [typst-of In Out Style]: the Typst source of the text In, in Out
  pred typst-of i:string, i:string, i:prooftext.formula-style.
  typst-of In Out Style :-
    prooftext.read-document In D,
    prooftext.write-typst-in Style D Text,
    open_out Out O, output O Text, close_out O,
    formula-counts Text All AsCode,
    coq.say {calc ("Typst: written " ^ Out ^ " (" ^ {std.any->string All} ^ " formulas, "
      ^ {std.any->string AsCode} ^ " shown as code)")}.

  % [formula-counts Text All AsCode]: the number of formulas in the Typst
  % source Text, and of those written as code (a call of a role's
  % function on a string, not on mathematics $...$)
  pred formula-counts i:string, o:int, o:int.
  formula-counts Text All AsCode :-
    occurrences "#\\(var\\|hyp\\|claim\\|fact\\|formula\\)(" Text All,
    occurrences "#\\(var\\|hyp\\|claim\\|fact\\|formula\\)(\"" Text AsCode.

  % [occurrences R S N]: the number of matches of the regexp R in S
  pred occurrences i:string, i:string, o:int.
  occurrences R S N :- rex.split R S Pieces, std.length Pieces L, N is L - 1.
}}.
Elpi Export Typst.
