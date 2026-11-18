Lists: ports, redo, modes, explanations, profile.

The four ports of each call, and a solution:

  $ elpi-debug -trace append.elpi 'rev [1,2] R'
  Call: #1 rev [1, 2] X0
  Unify: #1 with append.elpi:15: rev [1, 2] X0
    Call: #2 rev [2] X1
    Unify: #2 with append.elpi:15: rev [2] X1
      Call: #3 rev [] X2
      Unify: #3 with append.elpi:14: rev [] []
        X2 := []
      Exit: #3 rev [] []
      Call: #4 append [] [2] X1
      Unify: #4 with append.elpi:5: append [] [2] [2]
        X1 := [2]
      Exit: #4 append [] [2] [2]
    Exit: #2 rev [2] [2]
    Call: #5 append [2] [1] X0
    Unify: #5 with append.elpi:6: append [2] [1] [2 | X3]
        X0 := [2 | X3]
      Call: #6 append [] [1] X3
      Unify: #6 with append.elpi:5: append [] [1] [1]
        X3 := [1]
      Exit: #6 append [] [1] [1]
    Exit: #5 append [2] [1] [2, 1]
  Exit: #1 rev [1, 2] [2, 1]
  Solution 1:
    R = [2, 1]

Backtracking into a relation shows the redo ports:

  $ elpi-debug -trace -all append.elpi 'app X Y [1,2]'
  Call: #1 app X0 X1 [1, 2]
  Unify: #1 with append.elpi:10: app [] [1, 2] [1, 2]
        X0 := []
        X1 := [1, 2]
  Exit: #1 app [] [1, 2] [1, 2]
  Solution 1:
    X = []
    Y = [1, 2]
  Redo: #1 app [] [1, 2] [1, 2]
  Unify: #1 with append.elpi:11: app [1 | X2] X1 [1, 2]
        X0 := [1 | X2]
    Call: #2 app X2 X1 [2]
    Unify: #2 with append.elpi:10: app [] [2] [2]
        X2 := []
        X1 := [2]
    Exit: #2 app [] [2] [2]
  Exit: #1 app [1] [2] [1, 2]
  Solution 2:
    X = [1]
    Y = [2]
  Redo: #1 app [1] [2] [1, 2]
    Redo: #2 app [] [2] [2]
    Unify: #2 with append.elpi:11: app [2 | X3] X1 [2]
        X2 := [2 | X3]
      Call: #3 app X3 X1 []
      Unify: #3 with append.elpi:10: app [] [] []
        X3 := []
        X1 := []
      Exit: #3 app [] [] []
    Exit: #2 app [2] [] [2]
  Exit: #1 app [1, 2] [] [1, 2]
  Solution 3:
    X = [1, 2]
    Y = []
  Redo: #1 app [1, 2] [] [1, 2]
    Redo: #2 app [2] [] [2]
      Redo: #3 app [] [] []
      Fail: #3 app X3 X1 []
    Fail: #2 app X2 X1 [2]
  Fail: #1 app X0 X1 [1, 2]
  debug: no (more) solution.
  No goal failed at its first try: the query ran out of solutions by backtracking.

A failure explained: the clauses tried and the smallest clashing subterms.

  $ elpi-debug append.elpi 'append [1] [2] [3]'
  debug: no (more) solution.
  Deepest failure (depth 0): #1 append [1] [2] [3]
    clauses tried:
      append.elpi:5: append [] X0 X0
          does not match: argument 1 (input): [1] vs []
      append.elpi:6: append [X1 | X2] X3 [X1 | X4]
          does not match: argument 3 (output): [3] vs [1 | X4], at 3 vs 1
  No solution.

An input argument (i: or func) is matched, not unified, so a variable in
the goal does not match a clause head that needs a term:

  $ elpi-debug append.elpi 'append X [2] [1,2]'
  debug: no (more) solution.
  Deepest failure (depth 0): #1 append X1 [2] [1, 2]
    clauses tried:
      append.elpi:5: append [] X0 X0
          does not match: argument 1 (input): X1 vs [] (the goal has a variable where the clause expects a term: an input argument is only matched)
      append.elpi:6: append [X2 | X3] X4 [X2 | X5]
          does not match: argument 1 (input): X1 vs [X2 | X3] (the goal has a variable where the clause expects a term: an input argument is only matched)
  No solution.

The relation (all outputs) runs backwards; same answers as the real engine:

  $ elpi-debug -compare append.elpi 'app X Y [1,2,3]'
  Same answers (4).

A breakpoint on append (without -i: the context is printed at each stop):

  $ elpi-debug -break append append.elpi 'rev [1,2] R'
      Call: #4 append [] [2] X1
  --- breakpoint at #4: append [] [2] X1
    called from:
      #2 rev [2] X1
      #1 rev [1, 2] X0
    local program (clauses added by =>, most recent first):
    eigenvariables in scope: no eigenvariable
      Exit: #4 append [] [2] [2]
    Call: #5 append [2] [1] X0
  --- breakpoint at #5: append [2] [1] X0
    called from:
      #1 rev [1, 2] X0
    local program (clauses added by =>, most recent first):
    eigenvariables in scope: no eigenvariable
      Call: #6 append [] [1] X3
  --- breakpoint at #6: append [] [1] X3
    called from:
      #5 append [2] [1] [2 | X3]
      #1 rev [1, 2] [2 | X3]
    local program (clauses added by =>, most recent first):
    eigenvariables in scope: no eigenvariable
      Exit: #6 append [] [1] [1]
    Exit: #5 append [2] [1] [2, 1]
  Solution 1:
    R = [2, 1]

The profile (times masked, they vary):

  $ elpi-debug -profile append.elpi 'rev [1,2,3,4,5,6,7,8] R' | sed 's/  *[0-9]*\.[0-9][0-9]$/ T/'
  Profile (ports per predicate; tries = clauses tried; self time):
    predicate                        calls   exits   redos   fails   tries   time (ms)
    append                              36      36       0       0      64 T
    rev                                  9       9       0       0      17 T
  Solution 1:
    R = [8, 7, 6, 5, 4, 3, 2, 1]

The strategy can change: random order of the candidate clauses (seeded),
first solution of each call only, a depth bound (the strategy of a
generator, as in elpi-tools/check):

  $ for s in 1 2 3; do elpi-debug -random $s -first append.elpi 'app X Y [1,2,3]'; done
  Solution 1:
    X = []
    Y = [1, 2, 3]
  Solution 1:
    X = [1, 2, 3]
    Y = []
  Solution 1:
    X = []
    Y = [1, 2, 3]

  $ elpi-debug -max-depth 1 append.elpi 'app [1,2] Y Z'
  debug: no (more) solution.
  Deepest failure (depth 2): #3 app [] X0 X1
    called from:
      #2 app [2] X0 [2 | X1]
      #1 app [1, 2] X0 [1, 2 | X1]
    the depth bound stops it: calls deeper than 1 fail (option max-depth)
  No solution.
