// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "fr", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "fr"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Soient "#var($A , B : "Prop"$)#". Supposons "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#". Montrons "#claim($B ∨ A$)#"."]

#steps((
  step("1", [#"Montrons "#fact($B ∨ A$)#" par analyse de cas sur "#fact($A ∨ B$)#" "#name("h", target: "statement:h")#" ("#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#cited("or_ind", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind")#"):"], ()),
  step("2", [#"Cas 1: montrons "#claim($A → B ∨ A$)#"."], (
    step("2.1", [#"Supposons "#hyp($A$)#" "#name("i", label: "2.1:i")#"."], (
      step("2.1.1", [#"Par définition de "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_intror", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"), à partir de "#fact($A$)#" "#name("i", target: "2.1:i")#" nous en déduisons "#claim($B ∨ A$)#" "#by("Corelib.Init.Logic.or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"."], ()),
    )),
  )),
  step("3", [#"Cas 2: montrons "#claim($B → B ∨ A$)#"."], (
    step("3.1", [#"Supposons "#hyp($B$)#" "#name("j", label: "3.1:j")#"."], (
      step("3.1.1", [#"Par définition de "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_introl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"), à partir de "#fact($B$)#" "#name("j", target: "3.1:j")#" nous en déduisons "#claim($B ∨ A$)#" "#by("Corelib.Init.Logic.or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"."], ()),
    )),
  )),
  step("4", [#"Nous avons "#claim($B ∨ A$)#" dans tous les cas."], ()),
))

#legend((("var", "variable"), ("hyp", "hypothèse"), ("claim", "affirmation"), ("fact", "fait"), ("by", "justification"),))
