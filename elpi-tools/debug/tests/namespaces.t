Namespaces as Elpi >= 4.1.0 resolves them (not run with Elpi 4.0.x, which
resolves the names of a namespace block by block): in the second block of
n, p is n.p, m.r is n.m.r, lib is n.lib (namespaces_lib.elpi); in the
block of std, mem is std.mem; in n, the type term stays term.  The same
answer as Elpi itself:

  $ elpi-debug -compare namespaces.elpi main | tail -1
  Same answers (1).

The calls and the rules they use:

  $ elpi-debug -trace namespaces.elpi 'n.q, std.twice-mem [1,2] 2' | grep -E '^ *(Call|Exit):'
  Call: #1 n.q
    Call: #2 n.p   (premise 1 of namespaces.elpi:20)
    Exit: #2 n.p
    Call: #3 n.m.r   (premise 2 of namespaces.elpi:20)
    Exit: #3 n.m.r
    Call: #4 n.lib   (premise 3 of namespaces.elpi:20)
    Exit: #4 n.lib
  Exit: #1 n.q
  Call: #5 std.twice-mem [1, 2] 2
  Exit: #5 std.twice-mem [1, 2] 2
