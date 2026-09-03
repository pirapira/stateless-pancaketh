#!/usr/bin/env python3
"""bench.py GUEST.elf MANIFEST [--limit N] [--filter S] [--profile]
Gist-style benchmark: for each fixture, run spike_run (instruction count) and
ziskemu -X (steps, total cost, cost distribution) and print a table plus totals.
Only fixtures whose 69-byte output matches the expected bytes are counted as OK.

With --profile, the histogram-enabled tools/spike_prof/spike_prof runner is
used in place of spike_run and a top-15 per-function table is printed for each
fixture. Its ZisK cost column is an estimate based on the measured total cost
and each function's share of profiled Spike instructions.
"""
import argparse
import csv
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPIKE_RUN = os.environ.get("SPIKE_RUN", os.path.join(ROOT, "evm-asm/scripts/spike/spike_run"))
SPIKE_PROF = os.environ.get("SPIKE_PROF", os.path.join(ROOT, "tools/spike_prof/spike_prof"))
PROF_PY = os.path.join(ROOT, "tools/spike_prof/prof.py")
ZISKEMU = os.environ.get("ZISKEMU", os.path.expanduser("~/.zisk/bin/ziskemu"))

def resolve_input_path(path, manifest_dir):
    if os.path.isfile(path):
        return path
    return os.path.join(manifest_dir, os.path.basename(path))


def read_profile(elf, hist):
    proc = subprocess.run(
        [sys.executable, PROF_PY, elf, hist, "--top", "15", "--csv"],
        capture_output=True, text=True)
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip() or "unknown error"
        raise RuntimeError(f"prof.py failed: {detail}")
    return list(csv.DictReader(proc.stdout.splitlines()))


def print_profile(label, rows, total_cost):
    print(f"  profile: {label}")
    print(f"    {'function':60s} {'instructions':>12s} {'instr%':>8s} "
          f"{'est_zisk_cost':>14s} {'est_zisk_cost%':>14s}")
    for row in rows:
        name = row["function"]
        count = int(row["instructions"])
        instruction_share = float(row["instruction_share_pct"])
        if total_cost >= 0:
            estimated_cost = int(total_cost * instruction_share / 100 + 0.5)
            estimated_share = instruction_share
            cost_text = f"{estimated_cost:,}"
            share_text = f"{estimated_share:6.2f}%"
        else:
            cost_text = "?"
            share_text = "?"
        print(f"    {name[:60]:60s} {count:12d} {instruction_share:7.2f}% "
              f"{cost_text:>14s} {share_text:>14s}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("elf")
    ap.add_argument("manifest")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--filter", default="")
    ap.add_argument("--profile", action="store_true",
                    help="profile each fixture and print its top 15 functions")
    a = ap.parse_args()

    if a.profile and not os.path.isfile(SPIKE_PROF):
        ap.error(f"--profile requires {SPIKE_PROF}; run tools/spike_prof/build.sh")

    manifest_path = os.path.abspath(a.manifest)
    manifest_dir = os.path.dirname(manifest_path)
    with open(manifest_path) as manifest:
        rows = [l.rstrip("\n").split("\t") for l in manifest if l.strip()]
    for row in rows:
        row[1] = resolve_input_path(row[1], manifest_dir)
    if a.filter:
        rows = [r for r in rows if a.filter in r[0]]
    if a.limit:
        rows = rows[:a.limit]
    out_dir = os.path.join(ROOT, "work/bench")
    os.makedirs(out_dir, exist_ok=True)
    tot = dict(spike=0, steps=0, cost=0, ok=0, n=0)
    print(f"{'fixture':60s} {'ok':>3s} {'spike_instr':>12s} {'zisk_steps':>11s} "
          f"{'zisk_cost':>14s} {'main%':>6s} {'prec%':>6s} {'mem%':>5s}")
    for index, (label, inp, expected_hex, *_) in enumerate(rows):
        out = os.path.join(out_dir, label + ".out")
        hist = os.path.join(out_dir, f"profile-{index:05d}.hist")
        runner = SPIKE_RUN
        runner_env = None
        if a.profile:
            runner = SPIKE_PROF
            runner_env = dict(os.environ)
            runner_env["SPIKE_PC_HIST"] = hist
            if os.path.exists(hist):
                os.remove(hist)
        sp = subprocess.run([runner, a.elf, inp, out], capture_output=True,
                            text=True, env=runner_env)
        m = re.search(r"steps=(\d+)", sp.stderr)
        spike = int(m.group(1)) if m else -1
        ok = (os.path.exists(out)
              and open(out, "rb").read()[:len(expected_hex) // 2].hex() == expected_hex)
        z = subprocess.run([ZISKEMU, "-e", a.elf, "-i", inp, "-o", out + ".z", "-X"],
                           capture_output=True, text=True)
        txt = z.stdout + z.stderr

        def grab(pat):
            mm = re.search(pat, txt)
            return int(mm.group(1).replace(",", "")) if mm else -1

        steps = grab(r"STEPS\s+([\d,]+)")
        cost = grab(r"TOTAL\s+([\d,]+)")

        def pct(name):
            mm = re.search(name + r"\s+[\d,]+\s+([\d.]+)%", txt)
            return mm.group(1) if mm else "?"

        print(f"{label[:60]:60s} {('y' if ok else 'n'):>3s} {spike:12d} "
              f"{steps:11d} {cost:14d} {pct('MAIN'):>6s} "
              f"{pct('PRECOMPILES'):>6s} {pct('MEMORY'):>5s}")
        if a.profile:
            try:
                profile_rows = read_profile(a.elf, hist)
                print_profile(label, profile_rows, cost)
            except (OSError, RuntimeError, ValueError, KeyError) as exc:
                print(f"  profile unavailable: {exc}")
        tot["n"] += 1
        if ok:
            tot["ok"] += 1
            tot["spike"] += spike
            tot["steps"] += steps
            tot["cost"] += cost
    print(f"\nOK {tot['ok']}/{tot['n']}  spike_instr={tot['spike']}  "
          f"zisk_steps={tot['steps']}  zisk_cost={tot['cost']}"
          + (f"  cost/step={tot['cost'] / max(tot['steps'], 1):.1f}"
             if tot["steps"] else ""))


if __name__ == "__main__":
    main()
