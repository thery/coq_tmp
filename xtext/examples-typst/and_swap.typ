// The proof text and_swap, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("and_swap", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"Let "#var($A , B : "Prop"$)#". Assume "#hyp($A ∧ B$)#" "#name("H", label: "statement:H")#". We prove "#claim($B ∧ A$)#"."], (
  steps((
    step("1", [#"Going back to the definition of and (match) in "#just("H", target: "statement:H")#", we prove "#claim($B ∧ A$)#":"], (
      steps((
        step("1.1", [#"Assume "#hyp($A$)#" "#name("a", label: "1.1:a")#" and "#hyp($B$)#" "#name("b", label: "1.1:b")#". By definition of and ("#just("conj", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#conj")#"), from "#just("b", target: "1.1:b")#" and "#just("a", target: "1.1:a")#" we deduce "#claim($B ∧ A$)#"."], ()),
      )),
    )),
  )),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),))
