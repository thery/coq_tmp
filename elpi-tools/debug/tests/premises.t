Where each call comes from: the premise of the clause, at its call port
(the N-th goal of the body, nested conjunctions flattened as Elpi reads
them), also for a call made back by a builtin (std.forall) and for the
body of a hypothetical clause.

  $ elpi-debug -trace premises.elpi 'check [1]'
  Call: #1 check [1]
  Unify: #1 with premises.elpi:19: check [1]
    Call: #2 all-positive [1]   (premise 1 of premises.elpi:19)
    Unify: #2 with premises.elpi:10: all-positive [1]
      Call: #3 positive 1   (premise 1 of premises.elpi:10)
      Unify: #3 with premises.elpi:5: positive 1
      Exit: #3 positive 1
    Exit: #2 all-positive [1]
    Call: #4 twice 1 X0   (premise 2 of premises.elpi:19)
    Unify: #4 with premises.elpi:14: twice 1 X0
      Assume: pi c0 c1 \ twice c0 c1 :- c1 is c0 * 2 , positive c1   (added to the local program, for twice 1 X0 only)
      Call: #5 twice 1 X0   (premise 1 of premises.elpi:14)
      Unify: #5 with hypothesis added by #4: twice 1 X0
        Call: #6 positive 2   (premise 2 of hypothesis added by #4)
        Unify: #6 with premises.elpi:5: positive 2
        Exit: #6 positive 2
      Exit: #5 twice 1 2
        X0 := 2
    Exit: #4 twice 1 2
        X0 := 2
    Call: #7 positive 2   (premise 3 of premises.elpi:19)
    Unify: #7 with premises.elpi:5: positive 2
    Exit: #7 positive 2
  Exit: #1 check [1]
  Solution 1:

The place of each premise in the source (line, column to end line, end
column), in the description of a stop of -machine (the stop at the call
of all-positive, written on two lines):

  $ printf 'c\nc\nc\nc\n' | elpi-debug -machine premises.elpi 'check [1]' | grep '"stop":4' | sed -E 's|"/[^"]*/([^/"]+[.]elpi)"|"\1"|g; s/.*"frames":(.*),"bindings".*/\1/'
  [{"id":2,"goal":"all-positive [1]","clause":null,"premise":{"index":1,"clause":{"file":"premises.elpi","line":19},"place":{"file":"premises.elpi","line":20,"column":2,"endLine":21,"endColumn":5}},"args":[{"mode":"input","value":"[1]"}],"scope":[]},{"id":1,"goal":"check [1]","clause":{"file":"premises.elpi","line":19},"premise":null,"args":[{"mode":"input","value":"[1]"}],"scope":[]}]
