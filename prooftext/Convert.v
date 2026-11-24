(* The command [Convert "in.md" to "out.md" as free.] (or [as structured.]):
   the proof text in.md written again in out.md in the free style (prose,
   a node a span [ ... ]{.p} or a div ::: p ... :::) or in the structured
   style (one list item per node).  It reads the text with prooftext's
   reader (tree.elpi, read-tree: both styles give the same tree) and
   writes the tree with convert.elpi (write-free, write-structured); the
   lines before the body (header, title) are copied unchanged.  The rules
   are in README.md, "Converting between the two styles"; convert.sh runs
   the command.
   rocq c -Q ../lexicon Lexicon -Q . ProofText Convert.v *)
From elpi Require Import elpi.
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "tree.elpi" as pt_tree.
From ProofText Extra Dependency "nodes.elpi" as pt_nodes.
From ProofText Extra Dependency "convert.elpi" as pt_convert.

Elpi Command Convert.
Elpi Accumulate File lex_core pt_header pt_document pt_formulas pt_tree pt_nodes pt_convert.
Elpi Accumulate lp:{{
  main [str In, str "to", str Out, str "as", str Style] :- !, convert In Out Style.
  main _ :- coq.error "usage: Convert \"in.md\" to \"out.md\" as free.  (or as structured.)".

  % [convert In Out Style]: the text In written in Out in the style Style
  pred convert i:string, i:string, i:string.
  convert In Out "free" :- !, prooftext.write-free In Text, written In Out Text "free".
  convert In Out "structured" :- !, prooftext.write-structured In Text, written In Out Text "structured".
  convert _ _ S :- coq.error "Convert: no style" S "(free or structured)".

  pred written i:string, i:string, i:string, i:string.
  written In Out Text Style :-
    open_out Out O, output O Text, close_out O,
    coq.say {calc ("Convert: written " ^ Out ^ " (" ^ Style ^ ")")},
    (if (prooftext.same-tree In Text) true
        (coq.warning "prooftext" "convert" "Convert:" Out "read back has not the tree of" In
          "(the nodes and their tags differ: a [ that nothing closes in a text written free?)")).

}}.
Elpi Export Convert.
