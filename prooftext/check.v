(* Tests of prooftext: the writer of a document, the role tags, the
   justification, fresh names, tactic names; the reader, the marks of a
   checked text, the parts of a text and the strings of the Typst writer.
   rocq c -Q ../lexicon Lexicon -Q . ProofText check.v *)
From elpi Require Import elpi.
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "tree.elpi" as pt_tree.
From ProofText Extra Dependency "nodes.elpi" as pt_nodes.
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
    prooftext.justification-name "Nat.add_comm" JN, expect "justification name" JN "*Nat.add_comm*{.just}",
    (prooftext.is-justification J, ! ; coq.error "is-justification" J),
    prooftext.step-number "" 2 SN1, expect "step number 2" SN1 "2",
    prooftext.step-number "2.1" 3 SN2, expect "step number 2.1.3" SN2 "2.1.3",
    prooftext.field-value [prooftext.field "scope" "Z"] "scope" FV1, expect "field scope" FV1 "Z",
    prooftext.field-value [prooftext.field "scope" "Z"] "by" FV2, expect "no field by" FV2 "",
    prooftext.header-lang [prooftext.field "lang" "fr"] HL1, expect "lang fr" HL1 "fr",
    prooftext.header-lang [] HL2, expect "no lang" HL2 "en",
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
Elpi Accumulate File lex_core lex_en lex_fr pt_header pt_document pt_formulas pt_tree pt_nodes pt_checked
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
    prooftext.lines-tree Lines T0, prooftext.tree-document T0 D,
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

(* The tree (tree.elpi, nodes.elpi): the two syntaxes, structured (list
   items, the closing paragraph) and free (spans [ ... ]{.p}, divs ::: p),
   mixed; the justifications *X*{.just}; the remarks; each error of the
   reader, at its node and its line. *)
Elpi Command prooftext_check_tree.
Elpi Accumulate File lex_core pt_header pt_document pt_formulas pt_tree pt_nodes.
Elpi Accumulate lp:{{
  pred expect-term i:string, i:A, i:A.
  expect-term What Got Wanted :- if (Got = Wanted) (coq.say What ": ok")
    (coq.error What "gives" {std.any->string Got} "expected" {std.any->string Wanted}).

  % [tree-of Lines Top]: the top node of the text of Lines (a title first)
  pred tree-of i:list string, o:prooftext.node.
  tree-of Lines Top :- prooftext.lines-tree ["# t", "" | Lines] (prooftext.proof-text _ _ Top).

  % [shape Id N Shape]: the nodes of the proof in N, numbered from Id,
  % each "Id: its conclusions" (remarks left out)
  pred shape i:string, i:prooftext.node, o:list string.
  shape Id N [S | Ss] :-
    prooftext.node-parts N Ps, prooftext.claim-parts Ps Cs,
    std.map Cs prooftext.part-text Ts, std.string.concat ", " Ts T,
    S is Id ^ ": " ^ T,
    prooftext.node-children Id N Children,
    std.map Children (c\ s\ sigma I M\ c = pr I M, shape I M s) Sss, std.flatten Sss Ss.

  % [errors-of Lines Es]: the errors of the text of Lines, "Id line key"
  % (the lines of Lines numbered from 1, as in the messages)
  pred errors-of i:list string, o:list string.
  errors-of Lines Es :-
    tree-of Lines Top, prooftext.tree-errors Top Errors,
    std.map Errors (e\ s\ sigma I L K As\ e = prooftext.node-error I L (prooftext.text-error K As),
      s is I ^ " " ^ {std.any->string {calc (L - 1)} } ^ " " ^ K) Es.

  main [] :-
    % structured: the closing paragraph belongs to the item
    tree-of ["Let `E : Set`{.var}. Assume `P`{.hyp} (h). We prove `P /\\ P`{.claim}.", "",
      "- Let `x : E`{.var}; assume `Q x`{.hyp} (h1).",
      "  - By *h*{.just} we have `P`{.claim}.",
      "  - By *h1*{.just} we have `Q x`{.claim} (q).",
      "",
      "  So by *q*{.just} and *Nat.add_comm*{.just}, we have `P /\\ Q x`{.claim}.",
      "- Hence `P /\\ P`{.claim}."] T1,
    shape "0" T1 S1,
    expect-term "structured, closing paragraph" S1
      ["0: P /\\ P", "1: P /\\ Q x", "1.1: P", "1.2: Q x", "2: P /\\ P"],
    prooftext.node-children "0" T1 [pr _ N1 | _], prooftext.node-parts N1 Ps1,
    prooftext.justification-names Ps1 J1, expect-term "justifications" J1 ["q", "Nat.add_comm"],
    prooftext.hypothesis-names Ps1 H1, expect-term "hypotheses" H1 ["h1"],
    prooftext.variable-names Ps1 V1, expect-term "variables" V1 ["x"],
    prooftext.node-children "1" N1 [_, pr _ N12], prooftext.node-name "1.2" {prooftext.node-parts N12} Nm,
    expect-term "node name" Nm "q",
    prooftext.node-name "1.1" [] Auto, expect-term "auto name" Auto "c1_1",
    errors-of ["Let `E : Set`{.var}. Assume `P`{.hyp} (h). We prove `P /\\ P`{.claim}.", "",
      "- Let `x : E`{.var}; assume `Q x`{.hyp} (h1).",
      "  - By *h*{.just} we have `P`{.claim}.",
      "",
      "  So by *h1*{.just}, *c1_1*{.just} we have `P /\\ Q x`{.claim}."] E1,
    expect-term "no error" E1 [],
    % free: spans nest, a part goes to the innermost span; a ] inside a
    % formula, and a pair of brackets with no class, are text
    tree-of ["Let `x y z t : Prop`{.var}. If `x -> z`{.hyp} and `y -> t`{.hyp} then `(x /\\ y) -> (z /\\ t)`{.claim}.", "",
      "[Suppose `x /\\ y`{.hyp}. [[We have `x`{.claim}]{.p}, so by `x -> z`{.fact}",
      "we get `z`{.claim}.]{.p} [[We have `y`{.claim}]{.p}, so by `y -> t`{.fact}",
      "we get `t`{.claim} [as said].]{.p} Altogether we have `z /\\ t`{.claim}.]{.p}"] T2,
    shape "0" T2 S2,
    expect-term "free" S2 ["0: (x /\\ y) -> (z /\\ t)", "1: z /\\ t", "1.1: z", "1.1.1: x", "1.2: t", "1.2.1: y"],
    prooftext.numbered-subnodes "0" T2 [pr _ (prooftext.node O2 P2 M2 _ _)],
    expect-term "a span: its lines and its mark" (triple O2 P2 M2)
      (triple prooftext.bracketed (prooftext.lines 4 6) (prooftext.spot 4 1)),
    tree-of ["We prove `[1] = [1]`{.claim}: [by *eq_refl*{.just}, `[1] = [1]`{.claim}]{.p}."] T3,
    shape "0" T3 S3, expect-term "brackets in a formula" S3 ["0: [1] = [1]", "1: [1] = [1]"],
    % mixed: a list item holds a span; a div is a node of several paragraphs
    tree-of ["We prove `z`{.claim}.", "",
      "- [We have `x`{.claim}]{.p}, so by `x -> z`{.fact} we get `z`{.claim}.",
      "",
      "::: p",
      "Assume `y`{.hyp} (k).",
      "",
      "We have `y`{.claim} *by k*.",
      ":::"] T4,
    shape "0" T4 S4, expect-term "mixed, div" S4 ["0: z", "1: z", "1.1: x", "2: y"],
    prooftext.node-children "0" T4 [_, pr _ N4], prooftext.node-parts N4 Ps4,
    prooftext.justification-names Ps4 J4, expect-term "the transition form *by X*" J4 ["k"],
    % a remark: an item with no tag, shown, not a node; its sub-items are
    % those of the node around it
    tree-of ["We prove `A`{.claim}.", "",
      "- A remark, with `x` untagged and *emphasis*.",
      "  - We have `A`{.claim}."] T5,
    shape "0" T5 S5, expect-term "remark" S5 ["0: A", "1.1: A"],
    prooftext.numbered-subnodes "0" T5 [pr _ R5],
    (prooftext.is-remark R5, coq.say "is a remark: ok" ; coq.error "not a remark"),
    % the errors, at their nodes and lines
    errors-of ["Let `x : nat`{.var}. We prove `x = x`{.clam}."] Ea,
    expect-term "unknown class, no conclusion" Ea ["0 1 unknown-class", "0 1 statement-no-conclusion"],
    errors-of ["We prove `A`{.claim}.", "",
      "- Assume `A`{.hyp} (k).",
      "  - We have `A`{.claim} *by k*.",
      "- We have `A`{.claim} and `B`{.claim}, *by k*.",
      "- Assume `B`{.hyp} (k). By *m*{.just}, *a b*{.just} and *x*{.jsut} we have `A`{.claim}.",
      "  - Assume `C`{.hyp} (k). We have `A`{.claim}."] Eb,
    expect-term "node errors" Eb ["1 3 no-conclusion", "2 5 two-conclusions", "2 5 out-of-scope",
      "3 6 not-a-name", "3 6 unknown-class", "3.1 7 name-twice"],
    errors-of ["We prove `A`{.claim} here ]{.p}, there [`]`]{.x}, and [open.", "",
      ":::", "::: p", "We have `A`{.claim}.", "", "::: q", "We have `A`{.claim}."] Ec,
    expect-term "reader errors" Ec ["0 1 unopened-span", "0 1 unknown-class", "0 1 unclosed-span",
      "0 3 unopened-div", "1 4 unclosed-div", "1.1 7 unknown-class", "1.1 7 unclosed-div"].
}}.
Elpi prooftext_check_tree.

(* The links (links.elpi): a name given to a formula is a label, its uses
   (after a fact, in the text, in a justification) link to it, in its
   scope only; a word of the lexicon ("the") is never a name; a lemma of
   the corelib links to its documentation, a tactic does not; the
   legend, in the language of the text. *)
Elpi Command prooftext_check_links.
Elpi Accumulate File lex_core lex_en lex_fr pt_header pt_document pt_formulas pt_tree pt_nodes pt_checked
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
    expect-in "justification by a name" T "#just(\"a\", target: \"statement:a\")",
    expect-in "name in the text" T " By \"#named(\"h\", \"1.1:h\")",
    expect-not-in "a word of the lexicon" T "#named(\"the\"",
    expect-in "name of an earlier step" T "#named(\"P1\", \"1:P1\")",
    expect-in "name out of its scope" T "#\" and h, we have \"",
    expect-in "lemma in the text" T
      "#cited(\"conj\", \"https://rocq-prover.org/corelib/Corelib.Init.Logic.html#conj\")",
    expect-in "justification by a lemma" T
      "#just(\"Corelib.Init.Logic.conj\", url: \"https://rocq-prover.org/corelib/Corelib.Init.Logic.html#conj\")",
    expect-in "name after a fact" T "#name(\"a\", target: \"statement:a\")",
    expect-in "a tactic" T "#just(\"tauto\")",
    expect-in "legend" T
      "#legend(((\"var\", \"variable\"), (\"hyp\", \"hypothesis\"), (\"claim\", \"claim\"), (\"fact\", \"fact\"), (\"just\", \"justification\"),))",
    prooftext.legend-typst "fr" tt LegendFr,
    expect-in "legend in French, checked" LegendFr "(\"hyp\", \"hypothèse\")",
    expect-in "legend of the statuses" LegendFr "statuses: ((\"ok\", \"prouvé\")".
}}.
Elpi prooftext_check_links.

(* The Typst writer on a tree (typst.elpi): a checked free text, its
   spans (node) with their marks inline, cyp's messages in the order of
   the nodes, each with the status of its node (todo before ko here); a
   checked list item, its closing paragraph after its sub-item. *)
Elpi Command prooftext_check_typst_tree.
Elpi Accumulate File lex_core lex_en pt_header pt_document pt_formulas pt_tree pt_nodes pt_checked
  pt_maths_table pt_maths pt_maths_typst pt_links pt_typst.
Elpi Accumulate lp:{{
  pred expect-in i:string, i:string, i:string.
  expect-in What Text Part :-
    if (rex.split Part Text [_, _ | _]) (coq.say What ": ok")
      (coq.error What ": no" Part "in" Text).
  main [] :-
    rex.split "\n" {std.string.concat "\n" [
      "# free", "",
      "✅ Let `A : Prop`{.var}. Assume `A`{.hyp} (a). We prove `A`{.claim}.", "",
      "[🔶 **[1]** We have `A`{.claim} (P)]{.p} and [❌ by *P*{.just} `A`{.claim}]{.p}.", "",
      "<details><summary>left: A</summary></details>", "",
      "<details><summary>not proved: A</summary></details>", "",
      "- ✅ Assume `A`{.hyp} (b).", "  - ✅ We have `A`{.claim}.", "",
      "  Hence `A`{.claim}."]} Lines,
    prooftext.lines-tree Lines T,
    prooftext.write-typst-tree prooftext.code T Text,
    expect-in "statement, checked" Text "), status: \"ok\")",
    expect-in "a span, its mark inline" Text "#node(\"1\").#mark(\"todo\", conditions: \"1\")#\"We have \"",
    expect-in "the name of a span's conclusion, after it" Text "#just(\"P\", target: \"1:P\")",
    expect-in "the first message, of the first node" Text "message(\"todo\", \"left: A\"),",
    expect-in "the second message, of the second node" Text "message(\"ko\", \"not proved: A\"),",
    expect-in "the closing paragraph after the sub-item" Text
      "We have \"#claim(\"A\")#\".\"., (), status: \"ok\"),\n      )),\n      paragraph.#\"Hence \"".
}}.
Elpi prooftext_check_typst_tree.

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
