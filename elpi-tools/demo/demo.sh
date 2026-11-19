#!/bin/sh
# Runs every command of DEMO.md, in order (after `dune build` in
# elpi-tools/).
# Run it in an opam switch with elpi 4.1.1 or 4.0.0 (eval $(opam env --switch=...)).
cd "$(dirname "$0")" || exit 1
build=../_build/default
check="$build/check/bin/elpi_check_main.exe -I ../check/lib"
debug="$build/debug/bin/elpi_debug_main.exe -I ../check/lib"

# show the command, then run it
run() { echo; echo "\$ $*"; eval "$@"; }

echo "== 1. The properties: elpi-check finds the bug"
run "$check lambda.elpi"

echo; echo "== 2. The debugger: the reductions, and which clause gives the wrong one"
run "$debug -all lambda.elpi 'step (app (lam x\\ c) c) N'"
run "$debug -trace -all lambda.elpi 'step (app (lam x\\ c) c) N' | grep -E '^(Call|Unify|Redo|Exit): #1|^      X0|^Solution|^  N ='"

echo; echo "== 3. Why the reduced term has no type: the explanation of a failure"
run "$debug lambda.elpi 'of (lam x\\ c) base'"

echo; echo "== 4. λProlog in the trace: eigenvariables, hypotheses, their origin"
run "$debug -trace lambda.elpi 'of (lam x\\ lam y\\ x) T'"

echo; echo "== 5. Interactive stepping (commands fed on stdin)"
run "printf 'c\\nc\\nc\\nc\\nc\\nscope\\nhyps\\na\\n' | $debug -i -echo lambda.elpi 'of (lam x\\ lam y\\ x) T'"

echo; echo "== 6. A failure due to λProlog: self-application"
run "$debug lambda.elpi 'of (lam x\\ app x x) T'"

echo; echo "== 7. A predicate defined nowhere"
run "echo 'check [1,2]' | elpi nowhere.elpi 2>&1 | grep -v '^Parsing\\|^Compil\\|^Typecheck\\|^Determ\\|^\$\\|^goal>'"
run "$debug nowhere.elpi 'check [1,2]'"

echo; echo "== 8. The same answers as the real engine"
run "$debug -compare -all lambda.elpi 'step (app (lam x\\ c) c) N' | tail -1"

echo; echo "== 9. Lists: insertion sort with a wrong clause, and two reversals"
run "$check lists.elpi"
run "$debug -trace lists.elpi 'sort [0,0] S'"
run "$debug lists.elpi 'sort [0,0] [0,0]'"
run "$debug -profile lists.elpi 'std.iota 200 L, naive-rev L R1, rev L R2' | grep -v '^  [LR][12]* ='"
