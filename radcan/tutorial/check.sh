#!/usr/bin/env bash
# Compile every tutorial script against the current rocq/ files.
cd "$(dirname "$0")/../rocq" || exit 1
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=native --set-switch)"
tmp=$(mktemp -d); status=0
for f in ../tutorial/*.v ../paper/*.v; do
  cp "$f" "$tmp/"
  if rocq compile -w -notation-overridden,-ambiguous-paths,-deprecated -R . Radcan "$tmp/$(basename "$f")" >"$tmp/log" 2>&1
  then echo "ok   $f"; else echo "FAIL $f"; cat "$tmp/log"; status=1; fi
done
rm -rf "$tmp"; exit $status
