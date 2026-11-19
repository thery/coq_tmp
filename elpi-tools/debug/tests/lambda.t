Simply typed λ-calculus: pi and => with Elpi's own binders and local
program.

  $ for g in 'of (lam x\ lam y\ x) T' 'of (lam x\ app x x) T' 'of (app (lam x\ x) (lam y\ y)) T'; do elpi-debug -compare lambda.elpi "$g"; done
  Same answers (1).
  Same answers (0).
  Same answers (1).

  $ elpi-debug -trace lambda.elpi 'of (lam x\ lam y\ x) T'
  Call: #1 of (lam c0 \ lam c1 \ c0) X0
  Unify: #1 with lambda.elpi:14: of (lam c0 \ lam c1 \ c0) (arr X1 X2)
        X0 := arr X1 X2
    Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of (lam c1 \ x#1) X2
    Assume: of x#1 X1   (added to the local program, for of (lam c1 \ x#1) X2 only)
    Call: #2 of (lam c1 \ x#1) X2   (premise 1 of lambda.elpi:14)
    Unify: #2 with lambda.elpi:14: of (lam c1 \ x#1) (arr X3 X4)
        X2 := arr X3 X4
      Pi: x#2 is a new eigenvariable; its scope: (of x#2 X3) ==> of x#1 X4
      Assume: of x#2 X3   (added to the local program, for of x#1 X4 only)
      Call: #3 of x#1 X4   (premise 1 of lambda.elpi:14)
      Unify: #3 with hypothesis added by #1: of x#1 X1
        X4 := X1
      Exit: #3 of x#1 X1
        X4 := X1
    Exit: #2 of (lam c1 \ x#1) (arr X3 X1)
        X2 := arr X3 X1
  Exit: #1 of (lam c0 \ lam c1 \ c0) (arr X1 (arr X3 X1))
        X0 := arr X1 (arr X3 X1)
  Solution 1:
    T = arr X1 (arr X3 X1)

Self-application fails on the occurs check; the explanation shows the
hypothesis added for x and why it does not apply:

  $ elpi-debug lambda.elpi 'of (lam x\ app x x) T'
  debug: no (more) solution.
  Deepest failure (depth 2): #4 of c0 X0
    called from:
      #2 of (app c0 c0) X1
      #1 of (lam c1 \ app c1 c1) (arr (arr X0 X1) X1)
    clauses tried:
      hypothesis added by #1: of c0 (arr X0 X1)
          does not match: argument 2 (output): X0 vs arr X0 X1 (occurs check: X0 occurs in arr X0 X1)
      lambda.elpi:13: of (app X2 X3) X4
          does not match: argument 1 (input): c0 vs app X2 X3
      lambda.elpi:14: of (lam X5) (arr X6 X7)
          does not match: argument 1 (input): c0 vs lam X5
  No solution.

At a breakpoint: the ancestors, the hypothetical clauses in scope (with
the call that added them) and the eigenvariables:

  $ elpi-debug -break of lambda.elpi 'of (lam x\ lam y\ x) T'
  Call: #1 of (lam c0 \ lam c1 \ c0) X0
  --- breakpoint at #1: of (lam c0 \ lam c1 \ c0) X0
    called from:
    local program (clauses added by =>, most recent first):
    eigenvariables in scope: no eigenvariable
    Call: #2 of (lam c1 \ x#1) X1   (premise 1 of lambda.elpi:14)
  --- breakpoint at #2: of (lam c1 \ x#1) X1
    called from:
      #1 of (lam c1 \ lam c2 \ c1) (arr X2 X1)
    local program (clauses added by =>, most recent first):
      of x#1 X2    (hypothesis added by #1)
    eigenvariables in scope: x#1
      Call: #3 of x#1 X3   (premise 1 of lambda.elpi:14)
  --- breakpoint at #3: of x#1 X3
    called from:
      #2 of (lam c2 \ x#1) (arr X4 X3)
      #1 of (lam c2 \ lam c3 \ c2) (arr X2 (arr X4 X3))
    local program (clauses added by =>, most recent first):
      of x#2 X4    (hypothesis added by #2)
      of x#1 X2    (hypothesis added by #1)
    eigenvariables in scope: x#1, x#2
      Exit: #3 of x#1 X2
        X3 := X2
    Exit: #2 of (lam c1 \ x#1) (arr X4 X2)
        X1 := arr X4 X2
  Exit: #1 of (lam c0 \ lam c1 \ c0) (arr X2 (arr X4 X2))
        X0 := arr X2 (arr X4 X2)
  Solution 1:
    T = arr X2 (arr X4 X2)

Interactive: commands read from stdin (backtrace, hyps, step, continue).

  $ printf 'b\nh\ns\ns\ns\ns\ns\nc\n' | elpi-debug -i -break of lambda.elpi 'of (lam x\ lam y\ x) T'
  Call: #1 of (lam c0 \ lam c1 \ c0) X0
     ?     unknown command (h for help)
     ?     c or return  creep: go to the next event
      s            skip: run this call to its exit or fail without stopping inside
      o            out: run to the exit or fail of the call whose body runs this event
      l            leap: run to the next breakpoint
      t            trace: show every event, stop only at breakpoints
      n            nodebug: run to the end without stopping
      r            retry this call from its call port (bindings, local program, scope undone)
      r N          retry the call #N of the stack
      f            make this call fail
      p            print the goal, the local program and the scope
      g            the calls above (goals)
      scope        the eigenvariables in force and what each logic variable may depend on
      hyps         the local program: the clauses added by =>
      + P, - P     set, remove a breakpoint on the predicate P
      + clause N, - clause N   set, remove a breakpoint on the clause N (option -machine lists them)
      e            the deepest failure so far
      a            abort
     ?   Call: #2 of (lam c1 \ x#1) X1   (premise 1 of lambda.elpi:14)
     ?     Call: #3 of x#1 X3   (premise 1 of lambda.elpi:14)
     ?     Exit: #3 of x#1 X2
        X3 := X2
     ?   Exit: #2 of (lam c1 \ x#1) (arr X4 X2)
        X1 := arr X4 X2
     ? Exit: #1 of (lam c0 \ lam c1 \ c0) (arr X2 (arr X4 X2))
        X0 := arr X2 (arr X4 X2)
     ? Solution 1:
    T = arr X2 (arr X4 X2)
