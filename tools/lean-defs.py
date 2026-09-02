#!/usr/bin/env python3
"""Print a Lean file with theorem/#guard blocks stripped (for reading defs)."""
import sys, re
for path in sys.argv[1:]:
    out=[]; skip=False
    for line in open(path):
        if re.match(r'^(private |protected |@\[[^\]]*\] )*(theorem|lemma|example|instance)\b', line) or re.match(r'^#guard|^#eval', line):
            skip=True
        if skip:
            if line.strip()=='' : skip=False
            continue
        if line.strip()=='' : continue
        out.append(line.rstrip())
    print(f"===== {path}"); print("\n".join(out))
