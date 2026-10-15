#!/usr/bin/env bash
# Compile every tutorial script (and paper/*.v, tests/*.v) against rocq/
# files, JOBS at a time (default 8). Prints ok/FAIL per file, sorted.
cd "$(dirname "$0")/../rocq" || exit 1
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=native --set-switch)"
JOBS=${JOBS:-8}
out=$(mktemp -d)

check_one() {
  f=$1; out=$2
  d=$(mktemp -d); b=$(basename "$f")
  cp "$f" "$d/"
  if rocq compile -native-compiler no \
       -w -notation-overridden,-ambiguous-paths,-deprecated \
       -R . Radcan -R ../trig RadcanTrig "$d/$b" >"$d/log" 2>&1
  then echo "ok   $f" >"$out/$b.res"
  else { echo "FAIL $f"; cat "$d/log"; } >"$out/$b.res"; fi
  rm -rf "$d"
}
export -f check_one

ls ../tutorial/*.v ../paper/*.v ../tests/*.v ../doc/*.v | xargs -P "$JOBS" -I{} bash -c 'check_one "$1" "$2"' _ {} "$out"

cat "$out"/*.res
grep -q '^FAIL' "$out"/*.res; status=$((1 - $?))
rm -rf "$out"; exit $status
