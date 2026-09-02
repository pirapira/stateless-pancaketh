#!/usr/bin/env python3
"""bench.py GUEST.elf MANIFEST [--limit N] [--filter S]
Gist-style benchmark: for each fixture, run spike_run (instruction count) and
ziskemu -X (steps, total cost, cost distribution) and print a table plus totals.
Only fixtures whose 69-byte output matches the expected bytes are counted as OK."""
import argparse, os, re, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPIKE_RUN = os.environ.get("SPIKE_RUN", os.path.join(ROOT, "evm-asm/scripts/spike/spike_run"))
ZISKEMU = os.environ.get("ZISKEMU", os.path.expanduser("~/.zisk/bin/ziskemu"))
ap = argparse.ArgumentParser(); ap.add_argument("elf"); ap.add_argument("manifest")
ap.add_argument("--limit", type=int, default=0); ap.add_argument("--filter", default="")
a = ap.parse_args()
rows = [l.rstrip("\n").split("\t") for l in open(a.manifest) if l.strip()]
if a.filter: rows = [r for r in rows if a.filter in r[0]]
if a.limit: rows = rows[:a.limit]
out_dir = os.path.join(ROOT, "work/bench"); os.makedirs(out_dir, exist_ok=True)
tot = dict(spike=0, steps=0, cost=0, ok=0, n=0)
print(f"{'fixture':60s} {'ok':>3s} {'spike_instr':>12s} {'zisk_steps':>11s} {'zisk_cost':>14s} {'main%':>6s} {'prec%':>6s} {'mem%':>5s}")
for label, inp, expected_hex, *_ in rows:
    out = os.path.join(out_dir, label + ".out")
    sp = subprocess.run([SPIKE_RUN, a.elf, inp, out], capture_output=True, text=True)
    m = re.search(r"steps=(\d+)", sp.stderr); spike = int(m.group(1)) if m else -1
    ok = os.path.exists(out) and open(out, "rb").read()[:len(expected_hex)//2].hex() == expected_hex
    z = subprocess.run([ZISKEMU, "-e", a.elf, "-i", inp, "-o", out + ".z", "-X"], capture_output=True, text=True)
    txt = z.stdout + z.stderr
    def grab(pat):
        mm = re.search(pat, txt); return int(mm.group(1).replace(",", "")) if mm else -1
    steps = grab(r"STEPS\s+([\d,]+)"); cost = grab(r"TOTAL\s+([\d,]+)")
    def pct(name):
        mm = re.search(name + r"\s+[\d,]+\s+([\d.]+)%", txt); return mm.group(1) if mm else "?"
    print(f"{label[:60]:60s} {('y' if ok else 'n'):>3s} {spike:12d} {steps:11d} {cost:14d} {pct('MAIN'):>6s} {pct('PRECOMPILES'):>6s} {pct('MEMORY'):>5s}")
    tot["n"] += 1
    if ok: tot["ok"] += 1; tot["spike"] += spike; tot["steps"] += steps; tot["cost"] += cost
print(f"\nOK {tot['ok']}/{tot['n']}  spike_instr={tot['spike']}  zisk_steps={tot['steps']}  zisk_cost={tot['cost']}"
      + (f"  cost/step={tot['cost']/max(tot['steps'],1):.1f}" if tot['steps'] else ""))
