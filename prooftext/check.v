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
From ProofText Extra Dependency "maths-table.elpi" as pt_maths_table.
From ProofText Extra Dependency "maths.elpi" as pt_maths.
From ProofText Extra Dependency "maths-typst.elpi" as pt_maths_typst.
From ProofText Extra Dependency "links.elpi" as pt_links.
From ProofText Extra Dependency "typst.elpi" as pt_typst.
From Lexicon Extra Dependency "lang_en.elpi" as lex_en.
From Lexicon Extra Dependency "lang_fr.elpi" as lex_fr.

Elpi Command prooftext_check_typst.
Elpi Accumulate File lex_core lex_en lex_fr pt_header pt_document pt_formulas pt_checked
  pt_maths_table pt_maths pt_maths_typst pt_links pt_typst.
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
    expect-term "parts" Ps [prooftext.plain "From ", prooftext.formula-part "fact" "A" (some "i"),
      prooftext.plain " we deduce ",
      prooftext.formula-part "claim" "B \\/ A" none, prooftext.plain " ", prooftext.by-part "or_intror",
      prooftext.plain ", ", prooftext.formula-part "" "x" none, prooftext.plain " (y z)."],
    % a name after any number of spaces; a class that is no role's tag is
    % a class all the same; a backtick with no other after it is text
    prooftext.text-parts "Assume `A`{.hyp}  (h) and `B`{.Hyp}(k), `C" Ps2,
    expect-term "parts" Ps2 [prooftext.plain "Assume ", prooftext.formula-part "hyp" "A" (some "h"),
      prooftext.plain " and ", prooftext.formula-part "Hyp" "B" (some "k"),
      prooftext.plain ", `C"],
    prooftext.typst-string "a \\ \"b\"" TS, expect "typst string" TS "\"a \\\\ \\\"b\\\"\"".
}}.
Elpi prooftext_check_typst.

(* The links (links.elpi): a name given to a formula is a label, its uses
   (after a fact, in the text, in a justification) link to it, in its
   scope only; a word of the lexicon ("the") is never a name; a lemma of
   the corelib links to its documentation, a tactic does not; the
   legend, in the language of the text. *)
Elpi Command prooftext_check_links.
Elpi Accumulate File lex_core lex_en lex_fr pt_header pt_document pt_formulas pt_checked
  pt_maths_table pt_maths pt_maths_typst pt_links pt_typst.
Elpi Accumulate lp:{{
  % [expect-in What Text Part]: Part is in Text (Part read as a regexp
  % of rex: its dots match any character)
  pred expect-in i:string, i:string, i:string.
  expect-in What Text Part :-
    if (rex.split Part Text [_, _ | _]) (coq.say What ": ok")
      (coq.error What ": no" Part "in" Text).
  pred expect-not-in i:string, i:string, i:string.
  expect-not-in What Text Part :-
    if (rex.split Part Text [_, _ | _]) (coq.error What ":" Part "in" Text)
      (coq.say What ": ok").
  main [] :-
    U = prooftext.unplaced,
    D = prooftext.document [] "links" U
      "Let `A : Prop`{.var}. Assume `A`{.hyp} (a) and `A`{.hyp} (the). We prove `A /\\ A`{.claim}."
      [prooftext.step U "We have `A`{.claim} (P1) *by a*."
         [prooftext.step U "Assume `A`{.hyp} (h). By h and the we have `A`{.claim}." []],
       prooftext.step U "Applying conj to P1 and h, we have `A /\\ A`{.claim} *by Corelib.Init.Logic.conj*." [],
       prooftext.step U "From `A`{.fact} (a) we have `A`{.claim} *by tauto*." []],
    prooftext.write-typst-in prooftext.code D T,
    expect-in "label of a name of the statement" T "#name(\"a\", label: \"statement:a\")",
    expect-in "label of a name of a step" T "#name(\"P1\", label: \"1:P1\")",
    expect-in "justification by a name" T "#by(\"a\", target: \"statement:a\")",
    expect-in "name in the text" T " By \"#named(\"h\", \"1.1:h\")",
    expect-not-in "a word of the lexicon" T "#named(\"the\"",
    expect-in "name of an earlier step" T "#named(\"P1\", \"1:P1\")",
    expect-in "name out of its scope" T "#\" and h, we have \"",
    expect-in "lemma in the text" T
      "#cited(\"conj\", \"https://rocq-prover.org/corelib/Corelib.Init.Logic.html#conj\")",
    expect-in "justification by a lemma" T
      "#by(\"Corelib.Init.Logic.conj\", url: \"https://rocq-prover.org/corelib/Corelib.Init.Logic.html#conj\")",
    expect-in "name after a fact" T "#name(\"a\", target: \"statement:a\")",
    expect-in "a tactic" T "#by(\"tauto\")",
    expect-in "legend" T
      "#legend(((\"var\", \"variable\"), (\"hyp\", \"hypothesis\"), (\"claim\", \"claim\"), (\"fact\", \"fact\"),))",
    prooftext.legend-typst "fr" tt LegendFr,
    expect-in "legend in French, checked" LegendFr "(\"hyp\", \"hypothèse\")",
    expect-in "legend of the statuses" LegendFr "statuses: ((\"ok\", \"prouvé\")".
}}.
Elpi prooftext_check_links.

(* A lemma of the stdlib, in a module (Nat) of its file (PeanoNat) *)
From Stdlib Require Import Arith.
Elpi Command prooftext_check_stdlib_links.
Elpi Accumulate File lex_core pt_links.
Elpi Accumulate lp:{{
  main [] :-
    prooftext.documentation-url "Nat.lt_eq_cases" Url,
    if (Url = "https://rocq-prover.org/stdlib/Stdlib.Arith.PeanoNat.html#Nat.lt_eq_cases")
      (coq.say "documentation of Nat.lt_eq_cases: ok")
      (coq.error "documentation of Nat.lt_eq_cases:" Url),
    if (prooftext.documentation-url "lia" _) (coq.error "a tactic has a documentation") true.
}}.
Elpi prooftext_check_stdlib_links.
