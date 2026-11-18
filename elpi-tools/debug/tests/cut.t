The cut, as in the real engine: in a body, under pi and =>, inside ; and
inside not.  Each goal gives the same answers as the real engine.

  $ for g in 'first 1 [0,3,5] X' 'max-of 3 2 M' 'max-of 2 3 M' 'under-pi A' 'under-impl B' 'in-or C' 'not-mem 4 [1,2]' 'not-mem 1 [1,2]'; do echo "$g:"; elpi-debug -compare cut.elpi "$g"; done
  first 1 [0,3,5] X:
  Same answers (1).
  max-of 3 2 M:
  Same answers (1).
  max-of 2 3 M:
  Same answers (1).
  under-pi A:
  Same answers (1).
  under-impl B:
  Same answers (1).
  in-or C:
  Same answers (2).
  not-mem 4 [1,2]:
  Same answers (1).
  not-mem 1 [1,2]:
  Same answers (0).

The cut port: first commits to its clause after the first element > 1.

  $ elpi-debug -trace cut.elpi 'first 1 [0,3,5] X'
  Call: #1 first 1 [0, 3, 5] X0
  Unify: #1 with cut.elpi:9: first 1 [0, 3, 5] X0
    Call: #2 mem X0 [0, 3, 5]
    Unify: #2 with cut.elpi:4: mem 0 [0, 3, 5]
        X0 := 0
    Exit: #2 mem 0 [0, 3, 5]
    Redo: #2 mem 0 [0, 3, 5]
    Unify: #2 with cut.elpi:5: mem X0 [0, 3, 5]
      Call: #3 mem X0 [3, 5]
      Unify: #3 with cut.elpi:4: mem 3 [3, 5]
        X0 := 3
      Exit: #3 mem 3 [3, 5]
    Exit: #2 mem 3 [0, 3, 5]
  Cut: #1 commits to its current clause
  Exit: #1 first 1 [0, 3, 5] 3
  Solution 1:
    X = 3

A program predicate called from native code (not, here) still gets its
ports, through its bridge:

  $ elpi-debug -trace cut.elpi 'not-mem 1 [1,2]'
  Call: #1 not-mem 1 [1, 2]
  Unify: #1 with cut.elpi:33: not-mem 1 [1, 2]
    Call: #2 mem 1 [1, 2]
    Unify: #2 with cut.elpi:4: mem 1 [1, 2]
    Exit: #2 mem 1 [1, 2]
  Fail: #1 not-mem 1 [1, 2]
  debug: no (more) solution.
  Deepest failure (depth 1): not (mem 1 [1, 2])
    called from:
      #1 not-mem 1 [1, 2]
    a builtin (not a predicate of the program): it ran natively and failed
  No solution.
