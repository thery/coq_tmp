#!/bin/sh
# Run cyp on the given examples (copied to cyp-check/), with a time limit
# per text; print: name, seconds, proved, not proved, not checked (or
# "timeout").  usage: sh cyprun.sh LIMIT name...
lim=$1; shift
cd cyp-check
for f in "$@"; do
  cp ../examples/$f.md .
  rm -f $f.checked.md
  s=$(date +%s)
  CYP_ROCQ="${CYP_ROCQ:-rocq c -R /home/thery/git/coq_tmp/xtext XText}" timeout $lim \
    opam exec --root=/home/thery/opam-rocq.9.1.0 --switch=native -- \
    /home/thery/git/coq_tmp/cyp/_build/default/bin/cyp.exe $f.md >/dev/null 2>&1
  t=$(( $(date +%s) - s ))
  g=$f.checked.md
  if [ -f $g ]; then
    printf "%s\t%s\t%s\t%s\t%s\n" $f $t $(grep -c '^ *- ✅' $g) $(grep -c '^ *- ❌' $g) $(grep -c '^ *- ▫️' $g)
  else
    printf "%s\t%s\ttimeout\n" $f $t
  fi
done
