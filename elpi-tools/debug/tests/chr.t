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
    Call: #2 even X0
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
