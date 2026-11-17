#!/usr/bin/env python3
"""cyprun.py proof.md: check a cyp proof with Cyp File.

The driver of cyp (prototype of the OCaml one): from the header of the
proof, it writes a small .v file (its require: line, its rule files, then
`Elpi CypFile "proof.md".`) and runs rocq c on it.  The libraries, the
rules and the proof are read where they are; nothing is checked here.

Header fields used: require: (Rocq text), rules: (files .elpi, added to
cyp.db, or .v, copied), flags: (options of rocq c; -Q/-R/-I directories
relative to the proof).  The switch must have Elpi 4 and coq.parse.argument
(the switch elpi4), and the cyp library compiled in vernac/.
"""
import os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

def header(md):
    lines = open(md, encoding="utf-8").read().split("\n")
    h = {}
    if lines and lines[0].strip() == "---":
        for l in lines[1:]:
            if l.strip() == "---":
                break
            m = re.match(r"\s*([a-z]+):\s*(.*)$", l)
            if m:
                h[m.group(1)] = m.group(2).strip()
    return h

def main(md):
    md = os.path.abspath(md)
    d = os.path.dirname(md)
    h = header(md)
    flags = h.get("flags", "").split()
    for i in range(len(flags) - 1):
        if flags[i] in ("-Q", "-R", "-I") and not os.path.isabs(flags[i + 1]):
            flags[i + 1] = os.path.join(d, flags[i + 1])
    v = [h.get("require", ""), 'From CypV Require Import Cyp.']
    if "scope" in h:
        v.append("Open Scope %s." % h["scope"])
    deps = []
    for k, f in enumerate(h.get("rules", "").split()):
        f = os.path.join(d, f)
        if f.endswith(".elpi"):
            deps.append((k, f))
        else:
            v.append(open(f, encoding="utf-8").read())
    tmp = tempfile.mkdtemp(prefix="cyp-")
    for k, f in deps:
        os.symlink(f, os.path.join(tmp, "rules%d.elpi" % k))
        v.append('From CypRules Extra Dependency "rules%d.elpi" as cyp_rules%d.' % (k, k))
        v.append("Elpi Accumulate cyp.db File cyp_rules%d." % k)
    v.append('Elpi CypFile "%s".' % md)
    src = os.path.join(tmp, "cyp_check.v")
    open(src, "w", encoding="utf-8").write("\n".join(v) + "\n")
    cmd = ["rocq", "c", "-Q", HERE, "CypV", "-Q", tmp, "CypRules"] + flags + [src]
    r = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True)
    out = [l for l in (r.stdout + r.stderr).split("\n")
           if "cyp:" in l or "Error" in l]
    print("\n".join(out))
    return r.returncode

if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
