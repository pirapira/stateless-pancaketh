#!/usr/bin/env python3
"""prof.py ELF HIST  -- aggregate a spike_prof PC histogram per Pancake function."""
import subprocess, sys, bisect
elf, hist = sys.argv[1], sys.argv[2]
syms = []
for line in subprocess.check_output(['riscv64-unknown-elf-nm','-n',elf], text=True).splitlines():
    parts = line.split()
    if len(parts) == 3 and parts[1] in 'tT':
        syms.append((int(parts[0],16), parts[2]))
syms.sort(); addrs = [a for a,_ in syms]
agg = {}; total = 0
for line in open(hist):
    pc, n = line.split(); pc = int(pc,16); n = int(n)
    i = bisect.bisect_right(addrs, pc) - 1
    name = syms[i][1] if i >= 0 else '?'
    agg[name] = agg.get(name, 0) + n; total += n
print(f"total {total}")
for name, n in sorted(agg.items(), key=lambda x: -x[1])[:40]:
    print(f"{n:12d} {100*n/total:6.2f}% {name}")
