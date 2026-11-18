// The proof text and_swap, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("and_swap", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Let "#var("A B : Prop")#". Assume "#hyp("A /\\ B")#" "#name("H")#". We prove "#claim("B /\\ A")#"."]

#steps((
  step("1", [#"Going back to the definition of and (match) in "#fact("A /\\ B")#" "#name("H")#", we prove "#claim("B /\\ A")#":"], (
    step("1.1", [#"Assume "#hyp("A")#" "#name("a")#" and "#hyp("B")#" "#name("b")#"."], (
      step("1.1.1", [#"By definition of and (conj), from "#fact("B")#" "#name("b")#" and "#fact("A")#" "#name("a")#" we deduce "#claim("B /\\ A")#" "#by("Corelib.Init.Logic.conj")#"."], ()),
    )),
  )),
))
