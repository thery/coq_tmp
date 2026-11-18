// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "fr", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "fr"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Soient "#var("A B : Prop")#". Supposons "#hyp("A \\/ B")#" "#name("h")#". Montrons "#claim("B \\/ A")#"."]

#steps((
  step("1", [#"Montrons "#fact("B \\/ A")#" par analyse de cas sur "#fact("A \\/ B")#" "#name("h")#" (or, or_ind):"], ()),
  step("2", [#"Cas 1: montrons "#claim("A -> B \\/ A")#"."], (
    step("2.1", [#"Supposons "#hyp("A")#" "#name("i")#"."], (
      step("2.1.1", [#"Par définition de or (or_intror), à partir de "#fact("A")#" "#name("i")#" nous en déduisons "#claim("B \\/ A")#" "#by("Corelib.Init.Logic.or_intror")#"."], ()),
    )),
  )),
  step("3", [#"Cas 2: montrons "#claim("B -> B \\/ A")#"."], (
    step("3.1", [#"Supposons "#hyp("B")#" "#name("j")#"."], (
      step("3.1.1", [#"Par définition de or (or_introl), à partir de "#fact("B")#" "#name("j")#" nous en déduisons "#claim("B \\/ A")#" "#by("Corelib.Init.Logic.or_introl")#"."], ()),
    )),
  )),
  step("4", [#"Nous avons "#claim("B \\/ A")#" dans tous les cas."], ()),
))
