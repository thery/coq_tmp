(* The command [Typst "proof.md" to "proof.typ".]: the Typst source of a
   proof text (written by xtext, or checked by cyp), for its PDF.  It reads
   the Markdown with prooftext's reader (document.elpi) and writes it with
   write-typst (typst.elpi); pdf.sh runs it, then typst.
   rocq c -Q ../lexicon Lexicon -Q . ProofText Typst.v *)
From elpi Require Import elpi.
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "checked.elpi" as pt_checked.
From ProofText Extra Dependency "typst.elpi" as pt_typst.

Elpi Command Typst.
Elpi Accumulate File lex_core pt_header pt_document pt_formulas pt_checked pt_typst.
Elpi Accumulate lp:{{
  main [str In, str "to", str Out] :- !,
    prooftext.read-document In D,
    prooftext.write-typst D Text,
    open_out Out O, output O Text, close_out O,
    coq.say "Typst: written" Out.
  main _ :- coq.error "usage: Typst \"proof.md\" to \"proof.typ\".".
}}.
Elpi Export Typst.
