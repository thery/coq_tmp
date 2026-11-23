#!/bin/sh
# Checks that point_actions_tutorial.v is still true.
# 1. What the buttons do.  In the tutorial, a comment that says what to
#    select ends with a line
#      → LINE *)      (the line the last button named, click "Name", writes)
#    or
#      ✗ MESSAGE *)   (the error that button gives).
#    The table below gives, for each such comment, in the order of the
#    file, the name of the button, the selection as point_run takes it
#    (S E: characters S to E, blanks not counted, of the conclusion; H S
#    E: of the type of H; two for a link), the line, or !MESSAGE, and,
#    for the actions that point_actions_more.v declares too, what its
#    action of that name gives (empty: the same; -: not compared, for the
#    first steps of the tutorial's actions).  The check compiles a copy of
#    the tutorial where each comment is followed by
#      elpi point_run_expect "Name" "LINE" "" SEL.   or
#      (point_run "Name" SEL fails with MESSAGE)
#    point_run must give that very line, on the goal at that point,
#    without widening the selection, or fail with that message.  Then it
#    compiles a second copy, which loads point_actions_more.v (whose
#    actions come first, so that point_run runs them), with the lines of
#    the last column.
# 2. The messages.  A comment that starts with "(* prints:" gives the
#    messages of the sentence before it: the rest of its first line, or
#    its next lines without their first three blanks, up to "*)".  The
#    first copy prints a mark after each such comment; the messages
#    between two marks (between the start and the first mark, after the
#    last mark: none) must be the ones of the comment, runs of blanks
#    being compared as one space.
# 3. The references FILE.v:N of the comments: line N of FILE.v starts as
#    the table of the references says.
#   usage: sh point_actions_tutorial_check.sh  (from anywhere; exit 1 on a
#          difference).  Needs pbp.v, pbp_select.v, point_actions.v,
#          point_actions_more.v compiled, with the rocq of the current
#          opam switch.  The compilations are limited to 8 GB of virtual
#          memory, except with a rocq compiled by OCaml 5, which reserves
#          more address space than it uses: there, no limit.
here=$(cd "$(dirname "$0")" && pwd)
tut=$here/point_actions_tutorial.v
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
if rocq --version | grep -q "OCaml 4"; then ulimit -v 8000000; fi
status=0
me=point_actions_tutorial_check

# name|selection|line (or !message)|the line of point_actions_more.v, in
# the order of the tutorial
cat > "$tmp/table" <<'EOF'
Point|0 1|pbp [X in X /\ _].|
Link|"ab" 3 4 0 1|move: ab; pbp [X Y in (_ -> X) -> Y].|
Link|"a" 0 1 0 1|move: a; pbp [X Y in X -> Y].|
Link|"a" 0 1 0 1|move: a; pbp [X Y in X -> Y].|
Point|"h" 0 1|move: h; pbp [X in X \/ _ -> _].|
Link|"X" 0 1 3 4|move: X; pbp [X0 Y in X0 -> _ \/ Y].|
Link|"pbp" 0 1 0 1|move: pbp; pbp [X Y in X -> Y \/ _].|
Link|12 13 19 20|pbp [X Y in _ -> (_ -> X) -> _ -> Y].|
Link|"pbp" 3 4 0 1|move: pbp; pbp [X Y in (_ -> X) -> Y].|
Link|"pbp0" 0 1 0 1|move: pbp0; pbp [X Y in X -> Y].|
Simplify here|0 3|rewrite /=.|-
Simplify here|"H" 0 3|rewrite /= in H.|-
Simplify here|2 5|rewrite /=.|-
Simplify here|"H" 0 3|rewrite [X in X + _ = _]/= in H.|
Simplify here|2 5|rewrite [X in _ = X /\ _]/=.|
Simplify here|22 25|!the action Simplify here does not apply to the selection|-
Simplify here|22 25|!the selection uses a variable bound in the goal: introduce it first|rewrite [X in _ /\ (forall n : nat, f (X n) = _)]/=.
Simplify here|2 5|rewrite [X in _ = X /\ _]/=.|
Unfold here|0 11|rewrite [X in X = _]/double.|
Unfold here|"H" 0 7|rewrite [X in X = _]/double in H.|
Unfold here|12 21|rewrite [X in _ = X]/Nat.add.|
Unfold here|"H" 6 7|!the selection is not a constant nor an application of a constant|
EOF

# FILE.v:N|the start of that line
cat > "$tmp/refs" <<'EOF'
point_actions.v:64|pred point-action o:string
pbp_select.v:45|Definition pbp_hole
pbp_select.v:57|pred msg i:string
pbp_select.v:67|pred one-line i:string
pbp_select.v:266|pred parse-sels i:list argument
pbp_select.v:307|kind part type.
pbp_select.v:322|kind loc type.
pbp_select.v:443|kind point-in type.
pbp_select.v:453|pred point-resolve i:goal-ctx
EOF

# fails_with M t: the tactic t fails with a message that contains M,
# blanks ignored (Ltac2, which can read the message of a failure);
# tut_mark prints the mark
cat > "$tmp/tut_fail.v" <<'EOF'
From Ltac2 Require Import Ltac2.
From elpi Require Import elpi.
Ltac2 no_blanks (s : string) :=
  let rec go i acc :=
    if Int.lt i 0 then String.concat "" acc else
    let c := String.get s i in
    let n := Char.to_int c in
    if Bool.or (Bool.or (Int.equal n 32) (Int.equal n 10))
          (Bool.or (Int.equal n 9) (Int.equal n 13))
    then go (Int.sub i 1) acc
    else go (Int.sub i 1) (String.make 1 c :: acc) in
  go (Int.sub (String.length s) 1) [].
Ltac2 contains (s : string) (m : string) :=
  let ls := String.length s in
  let lm := String.length m in
  let rec from i :=
    if Int.lt (Int.sub ls lm) i then false
    else if String.equal (String.sub s i lm) m then true
    else from (Int.add i 1) in
  from 0.
Ltac2 fails_with (m : string) (t : unit -> unit) :=
  match Control.case t with
  | Val _ => Control.throw (Tactic_failure (Some (Message.of_string "no failure")))
  | Err e =>
      let s := Message.to_string (Message.of_exn e) in
      if contains (no_blanks s) (no_blanks m) then ()
      else Control.throw (Tactic_failure (Some (Message.concat
             (Message.of_string "unexpected message: ") (Message.of_string s))))
  end.
Elpi Command tut_mark.
Elpi Accumulate lp:{{ main [] :- coq.say "@@tut_mark@@". }}.
EOF

# ---- 1 and 2: the copies of the tutorial ----
# make_copy C: copy C (1: the tutorial's actions, with the marks; 2:
# those of point_actions_more.v)
make_copy() {
awk -v table="$tmp/table" -v copy="$1" -v prints="$tmp/prints" '
function esc(s) { gsub(/"/, "\"\"", s); return s }
function check(name, sel, line) {
  if (line ~ /^!/)
    printf "ltac2:(tut_fail.fails_with \"%s\" (fun () => ltac1:(elpi point_run \"%s\" %s))).\n", esc("point_run: " substr(line, 2)), esc(name), sel
  else
    printf "elpi point_run_expect \"%s\" \"%s\" \"\" %s.\n", esc(name), esc(line), sel
}
# the mark: in a proof a tactic (an Elpi command prints twice there)
function mark() {
  if (inproof) print "idtac \"@@tut_mark@@\"."; else print "Elpi tut_mark."
}
/^Proof\.$/ { inproof = 1 }
/^(Qed|Abort|Defined)\.$/ { inproof = 0 }
BEGIN {
  while ((getline l < table) > 0) {
    n++; split(l, f, "|"); tname[n] = f[1]; tsel[n] = f[2]; tline[n] = f[3]
    tmore[n] = f[4]
  }
}
inprints {
  print
  s = $0; end = sub(/ *\*\)$/, "", s); sub(/^   /, "", s)
  print s > prints
  if (end) { inprints = 0; print "--" > prints; if (copy == 1) mark() }
  next
}
/^\(\* prints:/ {
  print
  s = $0; sub(/^\(\* prints: */, "", s)
  if (sub(/ *\*\)$/, "", s)) {
    print s > prints; print "--" > prints
    if (copy == 1) mark()
  } else inprints = 1
  next
}
{ s = $0
  while (match(s, /click "[^"]*"/)) {
    last = substr(s, RSTART + 7, RLENGTH - 8); s = substr(s, RSTART + RLENGTH)
  } }
/^ *(\(\* )?(→|✗) .* \*\)$/ {
  print
  k++
  s = $0; sub(/^ *(\(\* )?/, "", s); sub(/ \*\)$/, "", s)
  fail = (s !~ /^→/)
  sub(/^(→|✗) /, "", s)
  if (fail) s = "!" s
  if (k > n) { print "more comments than entries in the table, at: " $0 > "/dev/stderr"; bad = 1; next }
  if (last != tname[k] || s != tline[k]) {
    printf "entry %d of the table, %s|%s, is not the comment, %s|%s\n", k, tname[k], tline[k], last, s > "/dev/stderr"
    bad = 1
  }
  if (copy == 1) check(tname[k], tsel[k], tline[k])
  else if (tmore[k] == "") check(tname[k], tsel[k], tline[k])
  else if (tmore[k] != "-") check(tname[k], tsel[k], tmore[k])
  last = ""
  next
}
/^From coq_tmp Require Import point_actions\.$/ {
  if (copy == 1) print; else print "From coq_tmp Require Import point_actions_more."
  print "From tut_check Require tut_fail."
  next
}
{ print }
END {
  if (k < n) { print "fewer comments (" k ") than entries in the table (" n ")" > "/dev/stderr"; bad = 1 }
  print k > (table ".count")
  exit bad
}
' "$tut"
}
make_copy 1 > "$tmp/tut_run.v" 2> "$tmp/err"
if [ $? -ne 0 ]; then
  echo "$me: the table and the comments differ:"; cat "$tmp/err"; status=1
fi
cp "$tmp/prints" "$tmp/prints1"
make_copy 2 > "$tmp/tut_more.v" 2> /dev/null
count=$(cat "$tmp/table.count" 2>/dev/null || echo 0)
more=$(awk -F'|' '$4 != "-"' "$tmp/table" | wc -l)
if [ "$status" -eq 0 ]; then
  if (cd "$tmp" && rocq c -R . tut_check tut_fail.v > out 2>&1 &&
      rocq c -w -elpi.linear-variable -R "$here" coq_tmp -R . tut_check tut_run.v > out 2> err); then
    echo "$me: the $count lines and errors of the buttons are the ones point_run gives"
    # the messages, between the marks
    awk -v me="$me" '
    function norm(s) { gsub(/[ \t\n]+/, " ", s); sub(/^ /, "", s); sub(/ $/, "", s); return s }
    FNR == NR { if ($0 == "--") { m++; want[m] = e; e = "" } else e = e "\n" $0; next }
    $0 == "@@tut_mark@@" { k++; got[k] = g; g = ""; next }
    { g = g "\n" $0 }
    END {
      if (k != m) { printf "%s: %d marks printed, %d comments with prints\n", me, k, m; exit 1 }
      for (i = 1; i <= m; i++)
        if (norm(got[i]) != norm(want[i])) {
          printf "%s: the messages before the mark %d are\n%s\nnot\n%s\n", me, i, got[i], want[i]; bad = 1 }
      if (norm(g) != "") { printf "%s: messages after the last mark:\n%s\n", me, g; bad = 1 }
      if (!bad) printf "%s: the messages of the %d sentences with prints are the ones promised\n", me, m
      exit bad
    }' "$tmp/prints1" "$tmp/out" || status=1
  else
    echo "$me: a line or an error is not the one point_run gives:"
    cat "$tmp/out" "$tmp/err"; status=1
  fi
  if (cd "$tmp" && rocq c -w -elpi.linear-variable -R "$here" coq_tmp -R . tut_check tut_more.v > out2 2>&1); then
    echo "$me: point_actions_more.v's actions give the lines of the last column on the $more selections compared"
  else
    echo "$me: point_actions_more.v's actions do not give the lines of the last column:"
    cat "$tmp/out2"; status=1
  fi
fi
# ---- 3. the references ----
nb=0
for r in $(grep -o '[a-z_]*\.v:[0-9][0-9]*' "$tut" | sort -u); do
  nb=$((nb + 1))
  start=$(grep -F "$r|" "$tmp/refs" | cut -d'|' -f2-)
  if [ -z "$start" ]; then echo "$me: the reference $r is not in the table"; status=1; continue; fi
  file=${r%%:*}; line=${r##*:}
  if ! sed -n "${line}p" "$here/$file" | grep -qF -- "$start"; then
    echo "$me: line $line of $file does not start with: $start"; status=1
  fi
done
[ "$status" -eq 0 ] && echo "$me: the $nb references FILE.v:N are the lines they name"
exit $status
