# Build the command and regenerate the examples (examples/*.md).
ROCQ = rocq c -R . XText

all: Explain.vo paper.vo lemmas.vo inductive.vo

Explain.vo: Explain.v xtext.elpi
	$(ROCQ) Explain.v

paper.vo: paper.v Explain.vo
	$(ROCQ) paper.v

lemmas.vo: lemmas.v Explain.vo
	$(ROCQ) lemmas.v

inductive.vo: inductive.v Explain.vo
	$(ROCQ) inductive.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all clean
