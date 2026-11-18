(* Tests of prooftext: the writer of a document, the role tags, the
   justification, fresh names, tactic names; the reader, the marks of a
   checked text, the parts of a text and the strings of the Typst writer.
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

(* The reader, the marks of a checked text, the Typst writer. *)
From ProofText Extra Dependency "checked.elpi" as pt_checked.
From ProofText Extra Dependency "typst.elpi" as pt_typst.

Elpi Command prooftext_check_typst.
Elpi Accumulate File lex_core pt_header pt_document pt_formulas pt_checked pt_typst.
Elpi Accumulate lp:{{
  pred expect i:string, i:string, i:string.
  expect What Got Wanted :- if (Got = Wanted) (coq.say What ": ok")
    (coq.error What "gives" Got "expected" Wanted).
  pred expect-term i:string, i:A, i:A.
  expect-term What Got Wanted :- if (Got = Wanted) (coq.say What ": ok")
    (coq.error What "gives" {std.any->string Got} "expected" {std.any->string Wanted}).
  main [] :-
    Text = {std.string.concat "\n" [
      "---", "require: From Stdlib Require Import Lia.", "lang: fr", "---", "",
      "# and_swap", "",
      "Let `A B : Prop`{.var}.", "We prove `A /\\ B -> B /\\ A`{.claim}.", "",
      "- Assume `A /\\ B`{.hyp} (h).",
      "  - We have `B /\\ A`{.claim}", "    *by tauto*.",
      "- We have proved `A /\\ B -> B /\\ A`{.claim}.", ""]},
    rex.split "\n" Text Lines,
    prooftext.lines-document Lines D,
    D = prooftext.document _ _ SP _ [prooftext.step P1 _ [prooftext.step P2 _ []], _],
    expect-term "places" [SP, P1, P2] [prooftext.lines 7 8, prooftext.lines 10 10, prooftext.lines 11 12],
    prooftext.write-document D Back,
    expect "read, written back" Back {std.string.concat "\n" [
      "---", "require: From Stdlib Require Import Lia.", "lang: fr", "---", "",
      "# and_swap", "",
      "Let `A B : Prop`{.var}. We prove `A /\\ B -> B /\\ A`{.claim}.", "",
      "- Assume `A /\\ B`{.hyp} (h).",
      "  - We have `B /\\ A`{.claim} *by tauto*.",
      "- We have proved `A /\\ B -> B /\\ A`{.claim}.", ""]},
    prooftext.split-checked "🔶 **[2a, 2b]** We have `C`{.claim}. <details><summary>not proved: C</summary></details>" C1 R1,
    expect-term "checked" C1 (prooftext.checked "todo" (some "2a, 2b") (some "not proved: C")),
    expect "checked text" R1 "We have `C`{.claim}.",
    (prooftext.split-checked "We have `C`{.claim}." _ _, coq.error "a text that is not checked" ; true),
    prooftext.text-parts "From `A`{.fact} (i) we deduce `B \\/ A`{.claim} *by or_intror*, `x` (y z)." Ps,
    expect-term "parts" Ps [prooftext.plain "From ", prooftext.formula-part "fact" "A",
      prooftext.plain " ", prooftext.name-part "i", prooftext.plain " we deduce ",
      prooftext.formula-part "claim" "B \\/ A", prooftext.plain " ", prooftext.by-part "or_intror",
      prooftext.plain ", ", prooftext.formula-part "" "x", prooftext.plain " (y z)."],
    prooftext.typst-string "a \\ \"b\"" TS, expect "typst string" TS "\"a \\\\ \\\"b\\\"\"".
}}.
Elpi prooftext_check_typst.
