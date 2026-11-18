Interactive stepping, as the box-model tracers of Prolog, with the events
of λProlog: the head unification of the selected clause (unify, with the
bindings it makes), the entry into pi (a new eigenvariable, named after
its binder) and into => (the clause added to the local program).  The
commands are fed on stdin; -echo prints each one after the prompt " ? ".

Creep through the typing of λx.λy.x, look at the scope and the local
program, print the focus, retry the inner call (its bindings, its
eigenvariable and its hypothesis are undone, then rebuilt), skip a call:

  $ printf 'c\nc\nc\nc\nscope\nhyps\nc\nc\nc\np\nr\nc\nc\nc\nc\nc\nc\ns\nc\nc\nc\n' | elpi-debug -i -echo lambda.elpi 'of (lam x\ lam y\ x) T'
  Call: #1 of (lam c0 \ lam c1 \ c0) X0
     ? c
  Unify: #1 with lambda.elpi:14: of (lam c0 \ lam c1 \ c0) (arr X1 X2)
        X0 := arr X1 X2
     ? c
    Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of (lam c1 \ x#1) X2
     ? c
    Assume: of x#1 X1   (added to the local program, for of (lam c1 \ x#1) X2 only)
     ? c
    Call: #2 of (lam c1 \ x#1) X2
     ? scope
    eigenvariables in force (oldest first): x#1
      X2 may depend on: no eigenvariable
     ? hyps
    local program (clauses added by =>, most recent first):
      of x#1 X1    (hypothesis added by #1)
     ? c
    Unify: #2 with lambda.elpi:14: of (lam c1 \ x#1) (arr X3 X4)
        X2 := arr X3 X4
     ? c
      Pi: x#2 is a new eigenvariable; its scope: (of x#2 X3) ==> of x#1 X4
     ? c
      Assume: of x#2 X3   (added to the local program, for of x#1 X4 only)
     ? p
    #2 of (lam c2 \ x#1) (arr X3 X4)
    local program (clauses added by =>, most recent first):
      of x#1 X1    (hypothesis added by #1)
    eigenvariables in force (oldest first): x#1, x#2
      X3 may depend on: no eigenvariable
      X4 may depend on: no eigenvariable
     ? r
      retry #2: back to its call port
    Call: #2 of (lam c1 \ x#1) X2
     ? c
    Unify: #2 with lambda.elpi:14: of (lam c1 \ x#1) (arr X5 X6)
        X2 := arr X5 X6
     ? c
      Pi: x#3 is a new eigenvariable; its scope: (of x#3 X5) ==> of x#1 X6
     ? c
      Assume: of x#3 X5   (added to the local program, for of x#1 X6 only)
     ? c
      Call: #3 of x#1 X6
     ? c
      Unify: #3 with hypothesis added by #1: of x#1 X1
        X6 := X1
     ? c
      Exit: #3 of x#1 X1
     ? s
    Exit: #2 of (lam c1 \ x#1) (arr X5 X1)
     ? c
  Exit: #1 of (lam c0 \ lam c1 \ c0) (arr X1 (arr X5 X1))
     ? c
  Solution 1:
    T = arr X1 (arr X5 X1)

Make a call fail, then leap to a breakpoint set at the prompt (removed
afterwards), and look at the calls above:

  $ printf 'c\nc\nc\nc\nf\nc\n+ same\nl\ng\n- same\nc\nc\nc\nc\nc\n' | elpi-debug -i -echo lambda.elpi '(of (app (lam x\ x) (lam y\ y)) T ; vacuous (x\ lam y\ y) M)'
  Call: #1 of (app (lam c0 \ c0) (lam c0 \ c0)) X0
     ? c
  Unify: #1 with lambda.elpi:13: of (app (lam c0 \ c0) (lam c0 \ c0)) X0
     ? c
    Call: #2 of (lam c0 \ c0) (arr X1 X0)
     ? c
    Unify: #2 with lambda.elpi:14: of (lam c0 \ c0) (arr X1 X0)
     ? c
      Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of x#1 X0
     ? f
    Fail: #2 of (lam c0 \ c0) (arr X1 X0)
     ? c
  Fail: #1 of (app (lam c0 \ c0) (lam c0 \ c0)) X0
     ? + same
    breakpoint on same
     ? l
    Call: #4 same (lam c1 \ c1) X9
     ? g
    called from:
      #3 vacuous (c1 \ lam c2 \ c2) X9
     ? - same
    no breakpoint on same
     ? c
    Unify: #4 with lambda.elpi:22: same (lam c1 \ c1) (lam c1 \ c1)
        X9 := lam c1 \ c1
     ? c
    Exit: #4 same (lam c1 \ c1) (lam c1 \ c1)
     ? c
  Exit: #3 vacuous (c0 \ lam c1 \ c1) (lam c0 \ c0)
     ? c
  Solution 1:
    M = lam c0 \ c0
    T = X0

A failure caused by the scope of an eigenvariable: M is created outside
pi x, so it cannot be x applied to itself; the unify port shows a
higher-order binding and a pruning:

  $ elpi-debug -trace lambda.elpi 'vacuous (x\ app x x) M'
  Call: #1 vacuous (c0 \ app c0 c0) X0
  Unify: #1 with lambda.elpi:19: vacuous (c0 \ app c0 c0) X0
    Pi: x#1 is a new eigenvariable; its scope: same (app x#1 x#1) X0
    Call: #2 same (app x#1 x#1) X0
    Fail: #2 same (app x#1 x#1) X0
  Fail: #1 vacuous (c0 \ app c0 c0) X0
  debug: no (more) solution.
  Deepest failure (depth 1): #2 same (app x#1 x#1) X0
    called from:
      #1 vacuous (c1 \ app c1 c1) X0
    clauses tried:
      lambda.elpi:22: same X1^1 X1^1
          does not match: argument 2 (output): X0 vs app x#1 x#1 (X0 cannot depend on the eigenvariable x#1, introduced by a pi after X0 was created)
  No solution.

  $ elpi-debug -trace lambda.elpi 'pi x\ same (F x) (app x x)'
  Pi: x#1 is a new eigenvariable; its scope: same (X0 x#1) (app x#1 x#1)
  Call: #1 same (X0 x#1) (app x#1 x#1)
  Unify: #1 with lambda.elpi:22: same (app x#1 x#1) (app x#1 x#1)
        X0 := c1 \ app c1 c1
  Exit: #1 same (app x#1 x#1) (app x#1 x#1)
  Solution 1:
    F = c0 \ app c0 c0

  $ elpi-debug -trace lambda.elpi 'pi x\ pi y\ same (G x) (F x y)'
  Pi: x#1 is a new eigenvariable; its scope: pi c1 \ same X0^1 (X1 x#1 c1)
  Pi: x#2 is a new eigenvariable; its scope: same X0^1 (X1 x#1 x#2)
  Call: #1 same X0^1 (X1 x#1 x#2)
  Unify: #1 with lambda.elpi:22: same (X4 x#1) (X4 x#1)
        X2 := c2 \ X3 c2
        X1 := c2 \ c3 \ X3 c2   (pruned: X4 gets 1 of the 2 arguments)
  Exit: #1 same (X4 x#1) (X4 x#1)
  Solution 1:
    F = c0 \ c1 \ X4 c0
    G = c0 \ X4 c0

Retry at a fail port: the call is run again from its call port (and fails
again); the help:

  $ printf 'c\nc\nc\nc\nr\nc\nc\nh\nn\n' | elpi-debug -i -echo -no-explain lambda.elpi 'vacuous (x\ x) M'
  Call: #1 vacuous (c0 \ c0) X0
     ? c
  Unify: #1 with lambda.elpi:19: vacuous (c0 \ c0) X0
     ? c
    Pi: x#1 is a new eigenvariable; its scope: same x#1 X0
     ? c
    Call: #2 same x#1 X0
     ? c
    Fail: #2 same x#1 X0
     ? r
      retry #2: back to its call port
    Call: #2 same x#1 X0
     ? c
    Fail: #2 same x#1 X0
     ? c
  Fail: #1 vacuous (c0 \ c0) X0
     ? h
      c or return  creep: go to the next event
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
     ? n
  No solution.

Suspended goals: each delay has a number, and the woken goal resumes with
the same number (as ECLiPSe's DELAY and RESUME ports):

  $ printf 'c\nc\nc\nc\nc\nc\nc\nc\nc\nc\nc\nc\n' | elpi-debug -i -echo chr.elpi 'even X, odd Y, X = 4, Y = 3'
  Call: #1 even X0
     ? c
  Unify: #1 with chr.elpi:10: even X0
     ? c
  Cut: #1 commits to its current clause
     ? c
    Delay: [S1] even X0 on [X0]
     ? c
  Exit: #1 even X0
     ? c
  Call: #2 odd X1
     ? c
  Unify: #2 with chr.elpi:14: odd X1
     ? c
  Cut: #2 commits to its current clause
     ? c
    Delay: [S2] odd X1 on [X1]
     ? c
  Exit: #2 odd X1
     ? c
    Resume: [S1] #3 even 4
     ? c
    Unify: #3 with chr.elpi:10: even 4
     ? c
    Unify: #3 with chr.elpi:11: even 4
     ? n
  Solution 1:
    X = 4
    Y = 3
