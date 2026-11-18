The machine-readable report of elpi-check (-json, lib/machine.elpi): one
JSON object per line.  The test programs are copied outside _build (the
replay goals are run by elpi-debug, whose file resolver is confused under
_build); the absolute paths of the files are masked.

  $ work=$(mktemp -d); cp *.elpi ../lib/property.elpi "$work"; cd "$work"
  $ mask () { sed -E 's|"/[^"]*/([^/"]+[.]elpi)"|"\1"|g'; }

The properties and their variables, without tests (-list):

  $ elpi-check -json -list stlc.elpi | mask
  {"event": "property", "name": "preservation", "file": "stlc.elpi", "line": 48, "variables": [{"name": "M", "type": "tm", "kind": "generated-by"}, {"name": "T", "type": "ty", "kind": "generated-by"}, {"name": "N", "type": "tm", "kind": "computed"}]}
  {"event": "property", "name": "preservation-wrong", "file": "stlc.elpi", "line": 52, "variables": [{"name": "M", "type": "tm", "kind": "generated-by"}, {"name": "T", "type": "ty", "kind": "generated-by"}, {"name": "N", "type": "tm", "kind": "computed"}]}
  {"event": "property", "name": "substitution", "file": "stlc.elpi", "line": 56, "variables": [{"name": "F", "type": "tm -> tm", "kind": "generated-by"}, {"name": "A", "type": "ty", "kind": "generated-by"}, {"name": "B", "type": "ty", "kind": "generated-by"}, {"name": "N", "type": "tm", "kind": "generated-by"}]}
  {"event": "property", "name": "copy-identity", "file": "stlc.elpi", "line": 61, "variables": [{"name": "M", "type": "tm", "kind": "generated"}, {"name": "N", "type": "tm", "kind": "computed"}]}
  {"event": "property", "name": "weakening", "file": "stlc.elpi", "line": 65, "variables": [{"name": "M", "type": "tm", "kind": "generated-by"}, {"name": "T", "type": "ty", "kind": "generated-by"}]}
  {"event": "property", "name": "all-typable", "file": "stlc.elpi", "line": 69, "variables": [{"name": "M", "type": "tm", "kind": "generated"}]}

Three properties of list reversal, one false: its first and shrunk
counterexamples, and the goal that replays the shrunk one:

  $ elpi-check -json rev.elpi | mask
  {"event": "property", "name": "rev-involutive", "file": "rev.elpi", "line": 15, "variables": [{"name": "L", "type": "list int", "kind": "generated"}, {"name": "R", "type": "list int", "kind": "computed"}, {"name": "L2", "type": "list int", "kind": "computed"}]}
  {"event": "result", "name": "rev-involutive", "file": "rev.elpi", "line": 15, "status": "ok", "passed": 100, "discarded": 0, "average-size": 10}
  {"event": "property", "name": "rev-append", "file": "rev.elpi", "line": 16, "variables": [{"name": "L1", "type": "list int", "kind": "generated"}, {"name": "L2", "type": "list int", "kind": "generated"}, {"name": "L", "type": "list int", "kind": "computed"}, {"name": "R", "type": "list int", "kind": "computed"}, {"name": "R1", "type": "list int", "kind": "computed"}, {"name": "R2", "type": "list int", "kind": "computed"}, {"name": "R3", "type": "list int", "kind": "computed"}]}
  {"event": "result", "name": "rev-append", "file": "rev.elpi", "line": 16, "status": "ok", "passed": 100, "discarded": 0, "average-size": 21}
  {"event": "property", "name": "rev-identity", "file": "rev.elpi", "line": 20, "variables": [{"name": "L", "type": "list int", "kind": "generated"}, {"name": "R", "type": "list int", "kind": "computed"}]}
  {"event": "result", "name": "rev-identity", "file": "rev.elpi", "line": 20, "status": "failed", "passed": 11, "discarded": 0, "failed-at-test": 12, "first": [{"name": "L", "value": "[-1, 1]"}, {"name": "R", "value": "[1, -1]"}], "shrunk": [{"name": "L", "value": "[0, 1]"}, {"name": "R", "value": "[1, 0]"}], "shrink-steps": 1, "replay": "rev [0, 1] R, R = [0, 1]"}
  {"event": "summary", "holds": 2, "properties": 3, "seed": 1}

A premise that discards, a false property shrunk in one step, a long
counterexample shrunk to eight zeros:

  $ elpi-check -json sort.elpi | mask
  {"event": "property", "name": "insert-sorted", "file": "sort.elpi", "line": 25, "variables": [{"name": "X", "type": "int", "kind": "generated"}, {"name": "L", "type": "list int", "kind": "generated"}, {"name": "R", "type": "list int", "kind": "computed"}]}
  {"event": "result", "name": "insert-sorted", "file": "sort.elpi", "line": 25, "status": "ok", "passed": 41, "discarded": 59, "average-size": 3}
  {"event": "property", "name": "insert-length", "file": "sort.elpi", "line": 29, "variables": [{"name": "X", "type": "int", "kind": "generated"}, {"name": "L", "type": "list int", "kind": "generated"}, {"name": "R", "type": "list int", "kind": "computed"}, {"name": "N", "type": "int", "kind": "computed"}, {"name": "M", "type": "int", "kind": "computed"}]}
  {"event": "result", "name": "insert-length", "file": "sort.elpi", "line": 29, "status": "failed", "passed": 37, "discarded": 0, "failed-at-test": 38, "first": [{"name": "X", "value": "7"}, {"name": "L", "value": "[7, -1]"}, {"name": "R", "value": "[7, -1]"}, {"name": "N", "value": "2"}, {"name": "M", "value": "2"}], "shrunk": [{"name": "X", "value": "7"}, {"name": "L", "value": "[7]"}, {"name": "R", "value": "[7]"}, {"name": "N", "value": "1"}, {"name": "M", "value": "1"}], "shrink-steps": 1, "replay": "insert-wrong 7 [7] R, std.length [7] N, std.length R M, M is (N + 1)"}
  {"event": "property", "name": "insert-length-right", "file": "sort.elpi", "line": 33, "variables": [{"name": "X", "type": "int", "kind": "generated"}, {"name": "L", "type": "list int", "kind": "generated"}, {"name": "R", "type": "list int", "kind": "computed"}, {"name": "N", "type": "int", "kind": "computed"}, {"name": "M", "type": "int", "kind": "computed"}]}
  {"event": "result", "name": "insert-length-right", "file": "sort.elpi", "line": 33, "status": "ok", "passed": 100, "discarded": 0, "average-size": 10}
  {"event": "property", "name": "short-lists", "file": "sort.elpi", "line": 38, "variables": [{"name": "L", "type": "list int", "kind": "generated"}, {"name": "N", "type": "int", "kind": "computed"}]}
  {"event": "result", "name": "short-lists", "file": "sort.elpi", "line": 38, "status": "failed", "passed": 43, "discarded": 0, "failed-at-test": 44, "first": [{"name": "L", "value": "[4, 3, -4, 0, 2, -2, -2, 1]"}, {"name": "N", "value": "8"}], "shrunk": [{"name": "L", "value": "[0, 0, 0, 0, 0, 0, 0, 0]"}, {"name": "N", "value": "8"}], "shrink-steps": 7, "replay": "std.length [0, 0, 0, 0, 0, 0, 0, 0] N, N < 8"}
  {"event": "summary", "holds": 2, "properties": 4, "seed": 1}

Values with binders, generated-by, a pi in the conclusion; the replay goal
of preservation-wrong pins N to the value of the counterexample (step-wrong
has another solution, which satisfies the conclusion):

  $ elpi-check -json stlc.elpi | mask
  {"event": "property", "name": "preservation", "file": "stlc.elpi", "line": 48, "variables": [{"name": "M", "type": "tm", "kind": "generated-by"}, {"name": "T", "type": "ty", "kind": "generated-by"}, {"name": "N", "type": "tm", "kind": "computed"}]}
  {"event": "result", "name": "preservation", "file": "stlc.elpi", "line": 48, "status": "ok", "passed": 38, "discarded": 62, "average-size": 60}
  {"event": "property", "name": "preservation-wrong", "file": "stlc.elpi", "line": 52, "variables": [{"name": "M", "type": "tm", "kind": "generated-by"}, {"name": "T", "type": "ty", "kind": "generated-by"}, {"name": "N", "type": "tm", "kind": "computed"}]}
  {"event": "result", "name": "preservation-wrong", "file": "stlc.elpi", "line": 52, "status": "failed", "passed": 0, "discarded": 5, "failed-at-test": 6, "first": [{"name": "M", "value": "app (lam (c0 \\ c)) c"}, {"name": "T", "value": "base"}, {"name": "N", "value": "lam (c0 \\ c)"}], "shrunk": [{"name": "M", "value": "app (lam (c0 \\ c)) c"}, {"name": "T", "value": "base"}, {"name": "N", "value": "lam (c0 \\ c)"}], "shrink-steps": 0, "replay": "of (app (lam (c0 \\ c)) c) base, step-wrong (app (lam (c0 \\ c)) c) N, N = lam (c0 \\ c), of N base"}
  {"event": "property", "name": "substitution", "file": "stlc.elpi", "line": 56, "variables": [{"name": "F", "type": "tm -> tm", "kind": "generated-by"}, {"name": "A", "type": "ty", "kind": "generated-by"}, {"name": "B", "type": "ty", "kind": "generated-by"}, {"name": "N", "type": "tm", "kind": "generated-by"}]}
  {"event": "result", "name": "substitution", "file": "stlc.elpi", "line": 56, "status": "ok", "passed": 100, "discarded": 0, "average-size": 38}
  {"event": "property", "name": "copy-identity", "file": "stlc.elpi", "line": 61, "variables": [{"name": "M", "type": "tm", "kind": "generated"}, {"name": "N", "type": "tm", "kind": "computed"}]}
  {"event": "result", "name": "copy-identity", "file": "stlc.elpi", "line": 61, "status": "ok", "passed": 100, "discarded": 0, "average-size": 6}
  {"event": "property", "name": "weakening", "file": "stlc.elpi", "line": 65, "variables": [{"name": "M", "type": "tm", "kind": "generated-by"}, {"name": "T", "type": "ty", "kind": "generated-by"}]}
  {"event": "result", "name": "weakening", "file": "stlc.elpi", "line": 65, "status": "ok", "passed": 100, "discarded": 0, "average-size": 41}
  {"event": "property", "name": "all-typable", "file": "stlc.elpi", "line": 69, "variables": [{"name": "M", "type": "tm", "kind": "generated"}]}
  {"event": "result", "name": "all-typable", "file": "stlc.elpi", "line": 69, "status": "failed", "passed": 14, "discarded": 0, "failed-at-test": 15, "first": [{"name": "M", "value": "app c c"}], "shrunk": [{"name": "M", "value": "app c c"}], "shrink-steps": 0, "replay": "is-closed (app c c), of (app c c) X0"}
  {"event": "summary", "holds": 4, "properties": 6, "seed": 1}

Strings are quoted in the values and in the replay goal:

  $ elpi-check -json strings.elpi | mask
  {"event": "property", "name": "shout-identity", "file": "strings.elpi", "line": 10, "variables": [{"name": "S", "type": "string", "kind": "generated"}, {"name": "T", "type": "string", "kind": "computed"}]}
  {"event": "result", "name": "shout-identity", "file": "strings.elpi", "line": 10, "status": "failed", "passed": 0, "discarded": 0, "failed-at-test": 1, "first": [{"name": "S", "value": "\"\""}, {"name": "T", "value": "\"!\""}], "shrunk": [{"name": "S", "value": "\"\""}, {"name": "T", "value": "\"!\""}], "shrink-steps": 0, "replay": "shout \"\" T, T = \"\""}
  {"event": "property", "name": "short-string-lists", "file": "strings.elpi", "line": 13, "variables": [{"name": "L", "type": "list string", "kind": "generated"}, {"name": "N", "type": "int", "kind": "computed"}]}
  {"event": "result", "name": "short-string-lists", "file": "strings.elpi", "line": 13, "status": "failed", "passed": 11, "discarded": 0, "failed-at-test": 12, "first": [{"name": "L", "value": "[\"\", \"\"]"}, {"name": "N", "value": "2"}], "shrunk": [{"name": "L", "value": "[\"\", \"\"]"}, {"name": "N", "value": "2"}], "shrink-steps": 0, "replay": "std.length [\"\", \"\"] N, N < 2"}
  {"event": "summary", "holds": 0, "properties": 2, "seed": 1}

A runtime error stops the run: the error event follows the announce of the
property being checked; the exit code is 2:

  $ elpi-check -json crash.elpi 2>/dev/null | mask
  {"event": "property", "name": "fine", "file": "crash.elpi", "line": 9, "variables": [{"name": "X", "type": "int", "kind": "generated"}]}
  {"event": "result", "name": "fine", "file": "crash.elpi", "line": 9, "status": "ok", "passed": 100, "discarded": 0, "average-size": 1}
  {"event": "property", "name": "crash", "file": "crash.elpi", "line": 10, "variables": [{"name": "X", "type": "int", "kind": "generated"}, {"name": "Y", "type": "int", "kind": "computed"}]}
  {"event":"error","message":"data: Evaluation of a non closed term. Maybe delay this predicate call and declare a constraint."}
  $ elpi-check -json crash.elpi > /dev/null 2>&1; echo "exit code $?"
  exit code 2

Every replay goal fails when elpi-debug runs it (the debugger shows why):

  $ for f in rev sort stlc strings; do
  >   elpi-check -json $f.elpi | sed -n 's/.*"replay": "\(.*\)"}$/\1/p' | sed 's/\\\\/\\/g; s/\\"/"/g' |
  >   while read -r goal; do echo "$f: $goal"; elpi-debug -no-explain $f.elpi "$goal" | tail -1; done
  > done
  rev: rev [0, 1] R, R = [0, 1]
  No solution.
  sort: insert-wrong 7 [7] R, std.length [7] N, std.length R M, M is (N + 1)
  No solution.
  sort: std.length [0, 0, 0, 0, 0, 0, 0, 0] N, N < 8
  No solution.
  stlc: of (app (lam (c0 \ c)) c) base, step-wrong (app (lam (c0 \ c)) c) N, N = lam (c0 \ c), of N base
  No solution.
  stlc: is-closed (app c c), of (app c c) X0
  No solution.
  strings: shout "" T, T = ""
  No solution.
  strings: std.length ["", ""] N, N < 2
  No solution.
