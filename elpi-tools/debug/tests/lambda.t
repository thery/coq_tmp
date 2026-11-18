Simply typed λ-calculus: pi and => with Elpi's own binders and local
program.

  $ for g in 'of (lam x\ lam y\ x) T' 'of (lam x\ app x x) T' 'of (app (lam x\ x) (lam y\ y)) T'; do elpi-debug -compare lambda.elpi "$g"; done
  Same answers (1).
  Same answers (0).
  Same answers (1).

  $ elpi-debug -trace lambda.elpi 'of (lam x\ lam y\ x) T'
  Call: #1 of (lam c0 \ lam c1 \ c0) X0
    Call: #2 of (lam c1 \ c0) X1
      Call: #3 of c0 X2
      Exit: #3 of c0 X3
    Exit: #2 of (lam c1 \ c0) (arr X4 X3)
  Exit: #1 of (lam c0 \ lam c1 \ c0) (arr X3 (arr X4 X3))
  Solution 1:
    T = arr X3 (arr X4 X3)

Self-application fails on the occurs check; the explanation shows the
hypothesis added for x and why it does not apply:

  $ elpi-debug lambda.elpi 'of (lam x\ app x x) T'
  debug: no (more) solution.
  Deepest failure (depth 2): #4 of c0 X1
    called from:
      #2 of (app c0 c0) X0
      #1 of (lam c1 \ app c1 c1) (arr (arr X1 X0) X0)
    clauses tried:
      hypothesis added by #1: of c0 (arr X1 X0)
          does not match: argument 2 (output): X1 vs arr X1 X0 (occurs check, or an eigenvariable out of scope)
      lambda.elpi:13: of (app X2^1 X3^1) X4^1
          does not match: argument 1 (input): c0 vs app X2^1 X3^1
      lambda.elpi:14: of (lam X5^1) (arr X6^1 X7^1)
          does not match: argument 1 (input): c0 vs lam X5^1
  No solution.

At a breakpoint: the ancestors, the hypothetical clauses in scope (with
the call that added them) and the eigenvariables:

  $ elpi-debug -break of lambda.elpi 'of (lam x\ lam y\ x) T'
  Call: #1 of (lam c0 \ lam c1 \ c0) X0
  --- stop at call #1: of (lam c0 \ lam c1 \ c0) X0
    called from:
    hypothetical clauses in scope (most recent first):
    eigenvariables in scope: []
    Call: #2 of (lam c1 \ c0) X1
  --- stop at call #2: of (lam c1 \ c0) X1
    called from:
      #1 of (lam c1 \ lam c2 \ c1) (arr X2 X1)
    hypothetical clauses in scope (most recent first):
      of c0 X2    (hypothesis added by #1)
    eigenvariables in scope: [c0]
      Call: #3 of c0 X3
  --- stop at call #3: of c0 X3
    called from:
      #2 of (lam c2 \ c0) (arr X4 X3)
      #1 of (lam c2 \ lam c3 \ c2) (arr X2 (arr X4 X3))
    hypothetical clauses in scope (most recent first):
      of c1 X4    (hypothesis added by #2)
      of c0 X2    (hypothesis added by #1)
    eigenvariables in scope: [c0, c1]
      Exit: #3 of c0 X2
    Exit: #2 of (lam c1 \ c0) (arr X4 X2)
  Exit: #1 of (lam c0 \ lam c1 \ c0) (arr X2 (arr X4 X2))
  Solution 1:
    T = arr X2 (arr X4 X2)

Interactive: commands read from stdin (backtrace, hyps, step, continue).

  $ printf 'b\nh\ns\ns\ns\ns\ns\nc\n' | elpi-debug -i -break of lambda.elpi 'of (lam x\ lam y\ x) T'
  Call: #1 of (lam c0 \ lam c1 \ c0) X0
  --- stop at call #1: of (lam c0 \ lam c1 \ c0) X0
  debug> (c)ontinue (s)tep (t)race (b)acktrace (h)yps (e)xplain (a)bort
    called from:
  debug> (c)ontinue (s)tep (t)race (b)acktrace (h)yps (e)xplain (a)bort
    hypothetical clauses in scope (most recent first):
    eigenvariables in scope: []
  debug> (c)ontinue (s)tep (t)race (b)acktrace (h)yps (e)xplain (a)bort
    try #1 lambda.elpi:13: of (app X1 X2) X3
    try #1 lambda.elpi:14: of (lam X4) (arr X5 X6)
    Call: #2 of (lam c1 \ c0) X6
  --- stop at call #2: of (lam c1 \ c0) X6
  debug> (c)ontinue (s)tep (t)race (b)acktrace (h)yps (e)xplain (a)bort
      try #2 hypothesis added by #1: of c0 X5
      try #2 lambda.elpi:13: of (app X7^1 X8^1) X9^1
      try #2 lambda.elpi:14: of (lam X10^1) (arr X11^1 X12^1)
      Call: #3 of c0 X13
  --- stop at call #3: of c0 X13
  debug> (c)ontinue (s)tep (t)race (b)acktrace (h)yps (e)xplain (a)bort
        try #3 hypothesis added by #2: of c1 X14
        try #3 hypothesis added by #1: of c0 X5
      Exit: #3 of c0 X5
  --- stop at exit #3: of c0 X5
  debug> (c)ontinue (s)tep (t)race (b)acktrace (h)yps (e)xplain (a)bort
    Exit: #2 of (lam c1 \ c0) (arr X14 X5)
  --- stop at exit #2: of (lam c1 \ c0) (arr X14 X5)
  debug> (c)ontinue (s)tep (t)race (b)acktrace (h)yps (e)xplain (a)bort
  Exit: #1 of (lam c0 \ lam c1 \ c0) (arr X5 (arr X14 X5))
  --- stop at exit #1: of (lam c0 \ lam c1 \ c0) (arr X5 (arr X14 X5))
  debug> (c)ontinue (s)tep (t)race (b)acktrace (h)yps (e)xplain (a)bort
  Solution 1:
    T = arr X5 (arr X14 X5)
