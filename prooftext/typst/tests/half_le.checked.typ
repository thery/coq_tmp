// The proof text half_le, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: true)

#title-block("half_le", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"Let "#var($n ∈ ℕ$)#". We prove "#claim($n class("binary", "div") 2 ≤ n$)#"."], (
  steps((
    step("1", [#"By definition of "#cited("nat", "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat")#" (strong_induction) on "#fact($n$)#", we prove "#claim($n class("binary", "div") 2 ≤ n$)#":"], (
      message("ko", "not proved: n / 2 <= n"),
      steps((
        step("1.1", [#"Let us choose arbitrarily "#var($n_(0) ∈ ℕ$)#"; assume by induction hypothesis "#hyp($∀ m ∈ ℕ , m < n_(0) → m class("binary", "div") 2 ≤ m$)#" "#name("IH", label: "1.1:IH")#"."], (
          steps((
            step("1.1.1", [#"The element "#fact($n_(0)$)#" belongs to "#fact($ℕ$)#"."], (), status: "none"),
            step("1.1.2", [#"The element "#fact($2$)#" belongs to "#fact($ℕ$)#"."], (), status: "none"),
            step("1.1.3", [#"The element "#fact($n_(0)$)#" belongs to "#fact($ℕ$)#"."], (), status: "none"),
            step("1.1.4", [#"Applying rew_iff_rev, we have "#claim($n_(0) ≤ 2 ⋅ n_(0)$)#"."], (
              steps((
                step("1.1.4.1", [#"The element "#fact($n_(0) ≤ 2 ⋅ n_(0)$)#" belongs to "#fact($"Prop"$)#"."], (), status: "none"),
                step("1.1.4.2", [#"The element "#fact($n_(0) ≤ "Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#" belongs to "#fact($"Prop"$)#"."], (), status: "none"),
                step("1.1.4.3", [#"Applying mkrel, we have "#claim($n_(0) ≤ 2 ⋅ n_(0) ↔ n_(0) ≤ "Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#"."], (
                  steps((
                    step("1.1.4.3.1", [#"The element "#fact($ℕ$)#" belongs to "#fact($"Type"$)#"."], (), status: "none"),
                    step("1.1.4.3.2", [#"The element "#fact($ℤ$)#" belongs to "#fact($"Type"$)#"."], (), status: "none"),
                    step("1.1.4.3.3", [#"The element "#fact($"le"$)#" belongs to "#fact($ℕ → ℕ → "Prop"$)#"."], (), status: "none"),
                    step("1.1.4.3.4", [#"The element "#fact($"of_nat"$)#" belongs to "#fact($ℕ → ℤ$)#"."], (), status: "none"),
                    step("1.1.4.3.5", [#"The element "#fact($"le"$)#" belongs to "#fact($ℤ → ℤ → "Prop"$)#"."], (), status: "none"),
                    step("1.1.4.3.6", [#"By inj_le we have "#claim($∀ n_(00) , m ∈ ℕ , n_(00) ≤ m ↔ n_(00) ≤ m$)#"."], (), status: "ok"),
                    step("1.1.4.3.7", [#"The element "#fact($n_(0)$)#" belongs to "#fact($ℕ$)#"."], (), status: "none"),
                    step("1.1.4.3.8", [#"The element "#fact($n_(0)$)#" belongs to "#fact($ℤ$)#"."], (), status: "none"),
                    step("1.1.4.3.9", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#cited("eq_refl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($n_(0) = n_(0)$)#" "#emph("by")#" "#just("Corelib.Init.Logic.eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"."], (), status: "ok"),
                    step("1.1.4.3.10", [#"The element "#fact($2 ⋅ n_(0)$)#" belongs to "#fact($ℕ$)#"."], (), status: "none"),
                    step("1.1.4.3.11", [#"The element "#fact($"Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#" belongs to "#fact($ℤ$)#"."], (), status: "none"),
                    step("1.1.4.3.12", [#"Applying mkapp2, we have "#claim($2 ⋅ n_(0) = "Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#"."], (
                      steps((
                        step("1.1.4.3.12.1", [#"The element "#fact($ℕ$)#" belongs to "#fact($"Type"$)#"."], (), status: "none"),
                        step("1.1.4.3.12.2", [#"The element "#fact($ℕ$)#" belongs to "#fact($"Type"$)#"."], (), status: "none"),
                        step("1.1.4.3.12.3", [#"The element "#fact($ℕ$)#" belongs to "#fact($"Type"$)#"."], (), status: "none"),
                        step("1.1.4.3.12.4", [#"The element "#fact($ℤ$)#" belongs to "#fact($"Type"$)#"."], (), status: "none"),
                        step("1.1.4.3.12.5", [#"The element "#fact($ℤ$)#" belongs to "#fact($"Type"$)#"."], (), status: "none"),
                        step("1.1.4.3.12.6", [#"The element "#fact($ℤ$)#" belongs to "#fact($"Type"$)#"."], (), status: "none"),
                        step("1.1.4.3.12.7", [#"The element "#fact($"mul"$)#" belongs to "#fact($ℕ → ℕ → ℕ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.8", [#"The element "#fact($"of_nat"$)#" belongs to "#fact($ℕ → ℤ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.9", [#"The element "#fact($"of_nat"$)#" belongs to "#fact($ℕ → ℤ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.10", [#"The element "#fact($"of_nat"$)#" belongs to "#fact($ℕ → ℤ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.11", [#"The element "#fact($"mul"$)#" belongs to "#fact($ℤ → ℤ → ℤ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.12", [#"By inj_mul we have "#claim($∀ n_(00) , m ∈ ℕ , n_(00) ⋅ m = n_(00) ⋅ m$)#"."], (), status: "ok"),
                        step("1.1.4.3.12.13", [#"The element "#fact($2$)#" belongs to "#fact($ℕ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.14", [#"The element "#fact($"Zpos"\("xO"\("xH"\)\)$)#" belongs to "#fact($ℤ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.15", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#cited("eq_refl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($"Zpos"\("xO"\("xH"\)\) = "Zpos"\("xO"\("xH"\)\)$)#" "#emph("by")#" "#just("Corelib.Init.Logic.eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"."], (), status: "ok"),
                        step("1.1.4.3.12.16", [#"The element "#fact($n_(0)$)#" belongs to "#fact($ℕ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.17", [#"The element "#fact($n_(0)$)#" belongs to "#fact($ℤ$)#"."], (), status: "none"),
                        step("1.1.4.3.12.18", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#cited("eq_refl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($n_(0) = n_(0)$)#" "#emph("by")#" "#just("Corelib.Init.Logic.eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"."], (), status: "ok"),
                      )),
                    ), status: "ok"),
                  )),
                ), status: "ok"),
                step("1.1.4.4", [#"Applying __arith, we have "#claim($n_(0) ≤ "Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#"."], (
                  steps((
                    step("1.1.4.4.1", [#"Applying is_nonneg to n0, we have "#claim($"Z0" ≤ n_(0)$)#" "#name("cstr", label: "1.1.4.4.1:cstr")#"."], (), status: "ok"),
                    step("1.1.4.4.2", [#"We have proved "#claim($∀ italic("__x10") ∈ ℤ , "eval_bf"\("Zeval_formula"\("find"\("Z0", "Elt"\(italic("__x10")\)\)\), "IMPL"\("A"\("isProp", "Build_Formula"\("PEc"\("Z0"\), "OpLe", "PEX"\("xH"\)\), "tt"\), "None", "A"\("isProp", "Build_Formula"\("PEX"\("xH"\), "OpLe", "PEmul"\("PEc"\("Zpos"\("xO"\("xH"\)\)\), "PEX"\("xH"\)\)\), "tt"\)\)\)$)#" "#name("__arith", label: "1.1.4.4.2:__arith")#"."], (
                      steps((
                        step("1.1.4.4.2.1", [#"Let us choose arbitrarily "#var($italic("__x1") ∈ ℤ$)#"."], (
                          steps((
                            step("1.1.4.4.2.1.1", [#"Let "#var($italic("__wit") ≔ "[]"$)#"."], (), status: "none"),
                            step("1.1.4.4.2.1.2", [#"Let "#var($italic("__varmap") ≔ "Elt"\(italic("__x1")\)$)#"."], (), status: "none"),
                            step("1.1.4.4.2.1.3", [#"Let "#var($italic("__ff") ≔ "IMPL"\("A"\("isProp", "Build_Formula"\("PEc"\("Z0"\), "OpLe", "PEX"\("xH"\)\), "tt"\), "None", "A"\("isProp", "Build_Formula"\("PEX"\("xH"\), "OpLe", "PEmul"\("PEc"\("Zpos"\("xO"\("xH"\)\)\), "PEX"\("xH"\)\)\), "tt"\)\)$)#"."], (), status: "none"),
                            step("1.1.4.4.2.1.4", [#"The element "#fact("__ff")#" belongs to "#fact($"BFormula"\("Formula"\(ℤ\), "isProp"\)$)#"."], (), status: "none"),
                            step("1.1.4.4.2.1.5", [#"The element "#fact("__wit")#" belongs to "#fact($"list"\("ZArithProof"\)$)#"."], (), status: "none"),
                            step("1.1.4.4.2.1.6", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#cited("eq_refl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($"true" = "true"$)#" "#emph("by")#" "#just("Corelib.Init.Logic.eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"."], (), status: "ok"),
                            step("1.1.4.4.2.1.7", [#"The element "#fact("VarMap.find BinNums.Z0 __varmap")#" belongs to "#fact($"PolEnv"\(ℤ\)$)#"."], (), status: "none"),
                            step("1.1.4.4.2.1.8", [#"Applying ZTautoChecker_sound, we have "#claim("Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff")#"."], (
                              message("ko", "not proved: Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff"),
                            ), status: "ko"),
                          )),
                        ), status: "none"),
                      )),
                    ), status: "ok"),
                    step("1.1.4.4.3", [#"The element "#fact($n_(0)$)#" belongs to "#fact($ℤ$)#"."], (), status: "none"),
                    step("1.1.4.4.4", [#"By "#named("cstr", "1.1.4.4.1:cstr")#" we have "#claim($"Z0" ≤ n_(0)$)#"."], (), status: "ok"),
                  )),
                ), status: "ok"),
              )),
            ), status: "ok"),
            step("1.1.5", [#"Applying div_le_upper_bound, we have "#claim($n_(0) class("binary", "div") 2 ≤ n_(0)$)#"."], (
              message("ko", "not proved: n0 / 2 <= n0"),
            ), status: "ko"),
          )),
        ), status: "none"),
      )),
    ), status: "ko"),
  )),
), status: "ok")

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),), statuses: (("ok", "proved"), ("ko", "not proved"), ("todo", "left to a Proof block"), ("none", "nothing to check"),))
