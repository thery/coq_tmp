(* Tests of prooftext: the writer of a document, the role tags, the
   justification, fresh names, tactic names.
   rocq c -Q ../lexicon Lexicon -Q . ProofText check.v *)
From elpi Require Import elpi.
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "names.elpi" as pt_names.
From ProofText Extra Dependency "tactics.elpi" as pt_tactics.

Elpi Command prooftext_check.
Elpi Accumulate File lex_core pt_header pt_document pt_formulas pt_names pt_tactics.
Elpi Accumulate lp:{{
  pred expect i:string, i:string, i:string.
  expect What Got Wanted :- if (Got = Wanted) (coq.say What ": ok")
    (coq.error What "gives" Got "expected" Wanted).
  main [] :-
    prooftext.formula rhyp "A /\\ B" F, expect "formula" F "`A /\\ B`{.hyp}",
    prooftext.role-tag R "claim", !, expect "tag claim" {std.any->string R} "rclaim",
    prooftext.justification "lia" J, expect "justification" J "*by lia*",
    (prooftext.is-justification J, ! ; coq.error "is-justification" J),
    prooftext.fresh-name ["h", "h0"] "h" N1, expect "fresh h" N1 "h1",
    prooftext.fresh-name ["h"] "x" N2, expect "fresh x" N2 "x",
    prooftext.unknown-tactics ["lia", "omega"] U, expect "unknown tactics" {std.any->string U} "[omega]",
    prooftext.lang-fields "fr" LF, prooftext.lang-fields "en" LE,
    prooftext.by-field ["tauto", "lia"] By,
    std.append [prooftext.field "require" "From Stdlib Require Import Lia." | LF] [By] Fields,
    D = prooftext.document Fields "and_swap" prooftext.unplaced
          "Let `A B : Prop`{.var}. We prove `A /\\ B -> B /\\ A`{.claim}."
          [prooftext.step prooftext.unplaced "Assume `A /\\ B`{.hyp} (h)."
             [prooftext.step prooftext.unplaced "We have `B /\\ A`{.claim} *by tauto*." []],
           prooftext.step prooftext.unplaced "We have proved `A /\\ B -> B /\\ A`{.claim}." []],
    prooftext.write-document D T,
    expect "lang en" {std.any->string LE} "[]",
    expect "document" T {std.string.concat "\n" [
      "---",
      "require: From Stdlib Require Import Lia.",
      "lang: fr",
      "by: tauto | lia",
      "---",
      "",
      "# and_swap",
      "",
      "Let `A B : Prop`{.var}. We prove `A /\\ B -> B /\\ A`{.claim}.",
      "",
      "- Assume `A /\\ B`{.hyp} (h).",
      "  - We have `B /\\ A`{.claim} *by tauto*.",
      "- We have proved `A /\\ B -> B /\\ A`{.claim}.",
      ""]}.
}}.
Elpi prooftext_check.
