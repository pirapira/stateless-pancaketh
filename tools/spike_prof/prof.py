#!/usr/bin/env python3
"""Aggregate a spike_prof PC histogram per Pancake function.

Usage: prof.py ELF HIST [--top N] [--csv]
"""
import argparse
import bisect
import csv
import subprocess
import sys


def aggregate(elf, hist):
    syms = []
    for line in subprocess.check_output(
            ["riscv64-unknown-elf-nm", "-n", elf], text=True).splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] in "tT":
            syms.append((int(parts[0], 16), parts[2]))
    syms.sort()
    addrs = [addr for addr, _ in syms]

    agg = {}
    total = 0
    with open(hist) as handle:
        for line in handle:
            if not line.strip():
                continue
            pc, count = line.split()
            pc = int(pc, 16)
            count = int(count)
            i = bisect.bisect_right(addrs, pc) - 1
            name = syms[i][1] if i >= 0 else "?"
            agg[name] = agg.get(name, 0) + count
            total += count
    return total, sorted(agg.items(), key=lambda item: -item[1])


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("elf")
    ap.add_argument("hist")
    ap.add_argument("--top", type=int, default=40, metavar="N",
                    help="number of functions to print (default: 40)")
    ap.add_argument("--csv", action="store_true",
                    help="write function,instructions,instruction_share_pct CSV")
    args = ap.parse_args(argv)
    if args.top < 0:
        ap.error("--top must be non-negative")

    total, rows = aggregate(args.elf, args.hist)
    rows = rows[:args.top]
    if args.csv:
        out = csv.writer(sys.stdout, lineterminator="\n")
        out.writerow(["function", "instructions", "instruction_share_pct"])
        for name, count in rows:
            share = 100 * count / total if total else 0
            out.writerow([name, count, f"{share:.2f}"])
        return 0

    print(f"total {total}")
    for name, count in rows:
        share = 100 * count / total if total else 0
        print(f"{count:12d} {share:6.2f}% {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
