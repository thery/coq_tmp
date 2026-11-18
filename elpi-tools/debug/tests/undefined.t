A predicate declared but defined nowhere: Elpi fails silently, the
debugger says so.

  $ elpi-debug -native undefined.elpi 'check [1,2]'
  No solution.

  $ elpi-debug undefined.elpi 'check [1,2]'
  debug warning: positive has no clause at all (in the program or in the hypotheses in scope); its calls fail
  debug: no (more) solution.
  Deepest failure (depth 1): #2 positive 1
    called from:
      #1 check [1, 2]
    positive is declared but has no clause at all (in the program or in the hypotheses in scope)
  No solution.

  $ elpi-debug -compare undefined.elpi 'check []'
  Same answers (1).
