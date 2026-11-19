CHR at depth 1: declare_constraint and the CHR rules are the engine's own;
a woken goal enters the interpreter through its Wake port.

  $ for g in 'even X, X = 4' 'even X, odd X' 'double 3 Y' 'even X, X = 3'; do elpi-debug -compare chr.elpi "$g"; done
  Same answers (1).
  CHR: both even and odd
  CHR: both even and odd
  Same answers (0).
  Same answers (1).
  Same answers (0).

  $ elpi-debug -trace chr.elpi 'double 3 Y'
  Call: #1 double 3 X0
  Unify: #1 with chr.elpi:18: double 3 X0
    Call: #2 even X0   (premise 1 of chr.elpi:18)
    Unify: #2 with chr.elpi:10: even X0
    Cut: #2 commits to its current clause
      Delay: [S1] even X0 on [X0]
    Exit: #2 even X0
      Resume: [S1] #3 even 6
      Unify: #3 with chr.elpi:10: even 6
      Unify: #3 with chr.elpi:11: even 6
      Exit: [S1] #3 even 6
  Exit: #1 double 3 6
        X0 := 6
  Solution 1:
    Y = 6

  $ elpi-debug -trace chr.elpi 'even X, odd X'
  Call: #1 even X0
  Unify: #1 with chr.elpi:10: even X0
  Cut: #1 commits to its current clause
    Delay: [S1] even X0 on [X0]
  Exit: #1 even X0
  Call: #2 odd X0
  Unify: #2 with chr.elpi:14: odd X0
  Cut: #2 commits to its current clause
    Delay: [S2] odd X0 on [X0]
    Rule: clause 6 chr.elpi:5 tried on [S1, S2]
    Rule: clause 6 chr.elpi:5 fires
  CHR: both even and odd
  Fail: #2 odd X0
  Redo: #1 even X0
  Fail: #1 even X0
  debug: no (more) solution.
  Deepest failure (depth 1): odd X0
    called from:
      #2 odd X0
    declare_constraint failed: adding this constraint fired a CHR rule that failed
  No solution.

CHR in view, on leq.elpi (order constraints: reflexivity and
antisymmetry simplify, transitivity propagates).  The answers are the
real engine's, with and without -trace (which rewrites the guards of the
rules to note their attempts); also on parity.elpi (in a namespace, a
rule that keeps a constraint and removes another, a rule that names a
context):

  $ for g in 'leq A B, leq B C, leq C A' 'leq A B, leq B A' 'leq A B, leq B C' 'leq A B, leq B C, A = 3, C = 2' 'leq A B, leq B C, A = 1, C = 2' 'chain 5 L' 'chain 4 [A,B,C,D], D = A'; do elpi-debug -compare leq.elpi "$g"; elpi-debug -compare -trace leq.elpi "$g" | tail -1; done
  Same answers (1).
  Same answers (1).
  Same answers (1).
  Same answers (1).
  Same answers (1).
  Same answers (1).
  Same answers (0).
  Same answers (0).
  Same answers (1).
  Same answers (1).
  Same answers (1).
  Same answers (1).
  Same answers (1).
  Same answers (1).
  $ for g in 'even X, X = 4' 'even X, odd X' 'double 3 Y' 'even X, X = 3'; do elpi-debug -compare -trace chr.elpi "$g" | tail -1; done
  Same answers (1).
  Same answers (0).
  Same answers (1).
  Same answers (0).
  $ for g in 'par.even X, par.odd X' 'par.even X, par.even X' 'par.even X, par.even X, X = 2'; do elpi-debug -compare parity.elpi "$g"; elpi-debug -compare -trace parity.elpi "$g" | tail -1; done
  Same answers (0).
  Same answers (0).
  Same answers (1).
  Same answers (1).
  Same answers (1).
  Same answers (1).

The attempts of the rules (those whose heads match: the numbers of the
constraints tried on), then their outcome: the guard fails, or the rule
fires (and removes the constraints after \); the goal of a rule that
fires runs in the interpreter, at the level of the query:

  $ elpi-debug -trace leq.elpi 'leq A B, leq B C, leq C A'
  Call: #1 leq X0 X1
  Unify: #1 with leq.elpi:13: leq X0 X1
  Cut: #1 commits to its current clause
    Delay: [S1] leq X0 X1 on [X0, X1]
    Rule: clause 7 leq.elpi:6 tried on [S1]
    Rule: clause 7 leq.elpi:6 guard fails
  Exit: #1 leq X0 X1
  Call: #2 leq X1 X2
  Unify: #2 with leq.elpi:13: leq X1 X2
  Cut: #2 commits to its current clause
    Delay: [S2] leq X1 X2 on [X1, X2]
    Rule: clause 7 leq.elpi:6 tried on [S2]
    Rule: clause 7 leq.elpi:6 guard fails
    Rule: clause 9 leq.elpi:8 tried on [S1, S2]
    Rule: clause 9 leq.elpi:8 fires
  Call: #3 leq X0 X2   (goal of the CHR rule at leq.elpi:8)
  Unify: #3 with leq.elpi:13: leq X0 X2
  Cut: #3 commits to its current clause
    Delay: [S3] leq X0 X2 on [X0, X2]
    Rule: clause 7 leq.elpi:6 tried on [S3]
    Rule: clause 7 leq.elpi:6 guard fails
  Exit: #3 leq X0 X2
  Exit: #2 leq X1 X2
  Call: #4 leq X2 X0
  Unify: #4 with leq.elpi:13: leq X2 X0
  Cut: #4 commits to its current clause
    Delay: [S4] leq X2 X0 on [X2, X0]
    Rule: clause 7 leq.elpi:6 tried on [S4]
    Rule: clause 7 leq.elpi:6 guard fails
    Rule: clause 8 leq.elpi:7 tried on [S4, S3]
    Rule: clause 8 leq.elpi:7 fires, removes [S4, S3]
    Resume: [S2] #5 leq X1 X0
    Unify: #5 with leq.elpi:13: leq X1 X0
    Cut: #5 commits to its current clause
      Delay: [S5] leq X1 X0 on [X1, X0]
      Rule: clause 7 leq.elpi:6 tried on [S5]
      Rule: clause 7 leq.elpi:6 guard fails
      Rule: clause 8 leq.elpi:7 tried on [S5, S1]
      Rule: clause 8 leq.elpi:7 fires, removes [S5, S1]
    Exit: [S2] #5 leq X0 X0
        X1 := X0
  Exit: #4 leq X0 X0
        X2 := X0
  Solution 1:
    A = X0
    B = X0
    C = X0

Interactive: a breakpoint on a CHR rule (+ clause N, the CHR rules
numbered after the rules: here 7 to 9), the store at a stop:

  $ printf '+ clause 9\nl\nstore\nc\nc\ng\nstore\n- clause 9\nl\n' | elpi-debug -i -echo leq.elpi 'leq A B, leq B C, leq C A'
  Call: #1 leq X0 X1
     ? + clause 9
    breakpoint on the clause at leq.elpi:8
     ? l
    Rule: clause 9 leq.elpi:8 tried on [S1, S2]
     ? store
    the constraint store (the goals suspended by declare_constraint, most recent first):
      [S2] leq X1 X2
      [S1] leq X0 X1
     ? c
    Rule: clause 9 leq.elpi:8 fires
     ? c
  Call: #3 leq X0 X2   (goal of the CHR rule at leq.elpi:8)
     ? g
    called from:
     ? store
    the constraint store (the goals suspended by declare_constraint, most recent first):
      [S2] leq X1 X2
      [S1] leq X0 X1
     ? - clause 9
    no breakpoint on the clause at leq.elpi:8
     ? l
  Solution 1:
    A = X0
    B = X0
    C = X0

With -machine: the CHR rules in the listing of the program, and at each
stop the store and, at a stop at a CHR rule, its location:

  $ printf '+ clause 9\nl\nn\n' | elpi-debug -machine leq.elpi 'leq A B, leq B C' | sed -E 's|"/[^"]*/([^/"]+[.]elpi)"|"\1"|g' | grep -o '"clauses":.*\]\|"text":"Rule[^"]*"\|"store":.*'
  "clauses":[{"clause":1,"predicate":"leq","file":"leq.elpi","line":13},{"clause":2,"predicate":"leq","file":"leq.elpi","line":14},{"clause":3,"predicate":"leq","file":"leq.elpi","line":15},{"clause":4,"predicate":"leq","file":"leq.elpi","line":16},{"clause":5,"predicate":"chain","file":"leq.elpi","line":20},{"clause":6,"predicate":"chain","file":"leq.elpi","line":21},{"clause":7,"predicate":"(CHR rule)","file":"leq.elpi","line":6},{"clause":8,"predicate":"(CHR rule)","file":"leq.elpi","line":7},{"clause":9,"predicate":"(CHR rule)","file":"leq.elpi","line":8}],"declarations":[{"file":"leq.elpi","line":12},{"file":"leq.elpi","line":19}]
  "store":[],"rule":null}
  "store":[],"rule":null}
  "text":"Rule: clause 9 leq.elpi:8 tried on [S1, S2]"
  "store":[{"suspension":2,"goal":"leq X1 X2"},{"suspension":1,"goal":"leq X0 X1"}],"rule":{"file":"leq.elpi","line":8}}
