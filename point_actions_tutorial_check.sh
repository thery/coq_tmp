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
#    E: of the type of H; two for a link) and the line, or !MESSAGE.  The
#    check first compares the table with the comments, then compiles a
#    copy of the tutorial where each comment is followed by
#      elpi point_run_expect "Name" "LINE" "" SEL.   or
#      Fail elpi point_run "Name" SEL.
#    point_run must give that very line, on the goal at that point,
#    without widening the selection, or fail with that message.
# 2. The excerpts: a comment that starts with a line
#      (* FILE, line N:      or      (* FILE, lines N-M:
#    and ends with a line *) holds exactly the lines N to M of FILE.
#   usage: sh point_actions_tutorial_check.sh  (from anywhere; exit 1 on a
#          difference).  Needs pbp.v, pbp_select.v, point_actions.v
#          compiled, with the rocq of the current opam switch.
here=$(cd "$(dirname "$0")" && pwd)
tut=$here/point_actions_tutorial.v
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
ulimit -v 8000000
status=0
me=point_actions_tutorial_check

# name|selection|line (or !message), in the order of the tutorial
cat > "$tmp/table" <<'EOF'
Point|0 1|pbp [X in X /\ _].
Link|"ab" 3 4 0 1|move: ab; pbp [X Y in (_ -> X) -> Y].
Link|"a" 0 1 0 1|move: a; pbp [X Y in X -> Y].
Simplify here|0 5|rewrite [X in X = _]/=.
Name occurrence|11 14|set x := {1}(c + b).
Name occurrence|"H" 0 3|set x := {1}(a + b) in H.
Where|0 1|idtac "[X in X + _ = _]  {1}  1  [2, 1]".
Where|6 7|idtac "[X in _ = _ + X]  {2}  2  [3, 2]".
Simplify here|"H" 0 3|rewrite [X in X + _ = _]/= in H.
Simplify (forward)|"H" 0 3|have H' := H; rewrite [X in X + _ = _]/= in H'.
Simplify (revert)|"H" 0 3|move: H; rewrite [X in X + _ = _ -> _]/=.
Name the others|2 3|set x := {-1}(a).
Name the others|0 1|!the selected term has no other copy
Commute (around)|"H" 0 3|move: H; rewrite [X in X = _ -> _]Nat.add_comm; move=> H.
Induction on this|0 1|elim: n.
Induction on this|0 3|!the selection is not a variable (elim: needs one)
Rewrite with this equation|"H" 2 5 7 10|rewrite -{1}H.
Rewrite with this equation|"H" 0 1 2 3|rewrite {2}H.
Commute here|11 14|rewrite [X in _ = _ + X]Nat.add_comm.
Commute here (Elpi)|11 14|rewrite [X in _ = _ + X]Nat.add_comm.
Case on this|1 6|case E: (n <=? m).
Generalize this|1 4|move: (a + b).
Name this|1 4|set x := (a + b).
Point|"H" 0 1|move: H; pbp [X in X /\ _ -> _].
Zero left|0 1|zero_left [X in X = _].
Zero left|"H" 0 1|move: H; zero_left [X in X + _ = _ -> _].
EOF

# fails_with M t: the tactic t fails with a message that contains M,
# blanks ignored (Ltac2, which can read the message of a failure)
cat > "$tmp/tut_fail.v" <<'EOF'
From Ltac2 Require Import Ltac2.
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
EOF

# ---- 1. what the buttons do ----
awk -v table="$tmp/table" '
function esc(s) { gsub(/"/, "\"\"", s); return s }
BEGIN {
  while ((getline l < table) > 0) {
    n++; split(l, f, "|"); tname[n] = f[1]; tsel[n] = f[2]; tline[n] = f[3]
  }
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
  if (fail)
    printf "ltac2:(tut_fail.fails_with \"%s\" (fun () => ltac1:(elpi point_run \"%s\" %s))).\n", esc("point_run: " substr(tline[k], 2)), esc(tname[k]), tsel[k]
  else
    printf "elpi point_run_expect \"%s\" \"%s\" \"\" %s.\n", esc(tname[k]), esc(tline[k]), tsel[k]
  last = ""
  next
}
/^From coq_tmp Require Import point_actions\.$/ { print; print "From tut_check Require tut_fail."; next }
{ print }
END {
  if (k < n) { print "fewer comments (" k ") than entries in the table (" n ")" > "/dev/stderr"; bad = 1 }
  print k > (table ".count")
  exit bad
}
' "$tut" > "$tmp/tut_run.v" 2> "$tmp/err"
if [ $? -ne 0 ]; then
  echo "$me: the table and the comments differ:"; cat "$tmp/err"; status=1
fi
count=$(cat "$tmp/table.count" 2>/dev/null || echo 0)
if [ "$status" -eq 0 ]; then
  if (cd "$tmp" && rocq c -R . tut_check tut_fail.v > out 2>&1 &&
      rocq c -R "$here" coq_tmp -R . tut_check tut_run.v > out 2>&1); then
    echo "$me: the $count lines and errors of the buttons are the ones point_run gives"
  else
    echo "$me: a line or an error is not the one point_run gives:"
    cat "$tmp/out"; status=1
  fi
fi
# ---- 2. the excerpts ----
awk -v dir="$here" -v tmp="$tmp" '
/^\(\* [A-Za-z_.]+\.v, lines? [0-9]+(-[0-9]+)?:$/ {
  s = $0; sub(/^\(\* /, "", s); sub(/:$/, "", s)
  i = index(s, ", line"); file = substr(s, 1, i - 1)
  r = substr(s, i + 6); sub(/^s? /, "", r)
  split(r, a, "-"); from = a[1]; to = (a[2] == "" ? a[1] : a[2])
  k++; out = tmp "/excerpt" k
  printf "%s %s %s %s\n", file, from, to, out > (tmp "/excerpts")
  printf "" > out
  inblock = 1; next
}
inblock && /^\*\)$/ { inblock = 0; close(out); next }
inblock { print > out }
' "$tut"
nb=0
while read -r file from to out; do
  nb=$((nb + 1))
  if ! sed -n "${from},${to}p" "$here/$file" | cmp -s - "$out"; then
    echo "$me: the excerpt of $file, lines $from-$to, is not in $file:"
    sed -n "${from},${to}p" "$here/$file" | diff - "$out"; status=1
  fi
done < "$tmp/excerpts"
[ "$status" -eq 0 ] && echo "$me: the $nb excerpts are verbatim in their files"
exit $status
