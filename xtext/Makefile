# Build the command and regenerate the examples (examples/*.md).
ROCQ = rocq c -R . XText -Q ../lexicon Lexicon -Q ../prooftext ProofText

all: ExtractText.vo paper.vo lemmas.vo inductive.vo thesis.vo stdlib.vo elim_type.vo partial.vo vocab_check.vo selection.vo subproofs.vo multilingual.vo typst_examples.vo implicit_motive.vo reals.vo printed.vo

../prooftext/Tactics.vo:
	cd ../prooftext && rocq c -Q . ProofText Tactics.v

ExtractText.vo: ../prooftext/Tactics.vo ExtractText.v $(wildcard elpi/*.elpi) $(wildcard ../lexicon/*.elpi) $(wildcard ../prooftext/*.elpi)
	$(ROCQ) ExtractText.v

paper.vo: paper.v ExtractText.vo
	$(ROCQ) paper.v

lemmas.vo: lemmas.v ExtractText.vo
	$(ROCQ) lemmas.v

inductive.vo: inductive.v ExtractText.vo
	$(ROCQ) inductive.v

thesis.vo: thesis.v ExtractText.vo
	$(ROCQ) thesis.v

stdlib.vo: stdlib.v ExtractText.vo
	$(ROCQ) stdlib.v

elim_type.vo: elim_type.v ExtractText.vo
	$(ROCQ) elim_type.v

partial.vo: partial.v ExtractText.vo
	$(ROCQ) partial.v

selection.vo: selection.v test-helpers.elpi ExtractText.vo thesis.vo
	$(ROCQ) selection.v

subproofs.vo: subproofs.v test-helpers.elpi ExtractText.vo thesis.vo
	$(ROCQ) subproofs.v

vocab_check.vo: vocab_check.v ExtractText.vo
	$(ROCQ) vocab_check.v

multilingual.vo: multilingual.v paper.vo lemmas.vo inductive.vo thesis.vo
	$(ROCQ) multilingual.v

typst_examples.vo: typst_examples.v paper.vo lemmas.vo inductive.vo
	$(ROCQ) typst_examples.v

implicit_motive.vo: implicit_motive.v test-helpers.elpi ExtractText.vo lemmas.vo
	$(ROCQ) implicit_motive.v

reals.vo: reals.v ExtractText.vo
	$(ROCQ) reals.v

printed.vo: printed.v ExtractText.vo lemmas.vo thesis.vo
	$(ROCQ) printed.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all clean
