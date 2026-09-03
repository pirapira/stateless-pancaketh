#!/usr/bin/env python3
"""Run a guest ELF over an EEST input manifest with spike_run and classify.

Usage: eest-run.py GUEST.elf MANIFEST.tsv [--jobs N] [--limit N] [--filter S]
                   [--out-dir DIR] [--quiet-passes] [--ziskemu]
                   [--json FILE] [--from-json FILE --fail-code CLASS/CODE]
                   [--labels FILE]

Classification mirrors evm-asm/scripts/eest-specref-check.sh:
  root = bytes 0:32, succ = byte 32, tail = bytes 33:69 (69-byte results);
  other lengths are compared byte-for-byte ("malformed" sentinel path).
Also records the consumed instruction count reported by spike_run
("halted cleanly steps=N") per case and prints a summary.
"""
import argparse, os, re, subprocess, sys, json, time
from concurrent.futures import ThreadPoolExecutor
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPIKE_RUN = os.environ.get("SPIKE_RUN", os.path.join(ROOT, "evm-asm/scripts/spike/spike_run"))
ZISKEMU = os.environ.get("ZISKEMU", os.path.expanduser("~/.zisk/bin/ziskemu"))
STEPS_RE = re.compile(r"halted cleanly steps=(\d+)")

def resolve_input_path(path, manifest_dir):
    if os.path.isfile(path):
        return path
    return os.path.join(manifest_dir, os.path.basename(path))

def run_case(elf, row, out_dir, use_zisk):
    label, inp, expected_hex = row[0], row[1], row[2]
    out = os.path.join(out_dir, label + ".output")
    log = os.path.join(out_dir, label + ".log")
    t0 = time.time()
    env = dict(os.environ)
    env.setdefault("SPIKE_OUTPUT_LEN", "256")
    if use_zisk:
        cmd = [ZISKEMU, "-e", elf, "-i", inp, "-o", out, "-m"]
    else:
        cmd = [SPIKE_RUN, elf, inp, out]
    with open(log, "w") as lf:
        rc = subprocess.call(cmd, stdout=lf, stderr=subprocess.STDOUT, env=env)
    dt = time.time() - t0
    steps = None
    logtxt = open(log, errors="replace").read()
    m = STEPS_RE.search(logtxt)
    if m: steps = int(m.group(1))
    if use_zisk:
        m = re.search(r"steps[=: ]+(\d+)", logtxt)
        if m: steps = int(m.group(1))
    actual = ""; dbg = -1
    if os.path.exists(out):
        raw = open(out, "rb").read()
        # output region is zero-padded to SPIKE_OUTPUT_LEN; the SSZ result
        # length is 69 (normal) or 61 (sentinel). Trim by expected length.
        n = len(expected_hex) // 2
        actual = raw[:n].hex()
        dbg = raw[n] if len(raw) > n else 0   # guest debug bytes: fail class, code
        if len(raw) > n + 1: dbg = f"{dbg}/{raw[n+1]}"
    return dict(label=label, rc=rc, steps=steps, secs=dt, expected=expected_hex, actual=actual, dbg=dbg)

def classify(r):
    e, a = r["expected"], r["actual"]
    if r["rc"] != 0 or not a:
        return "ERROR", ""
    if len(e) != 138:
        return ("PASS(malformed)" if e == a else "FAIL[malformed]"), ""
    root = e[0:64] == a[0:64]; succ = e[64:66] == a[64:66]; tail = e[66:138] == a[66:138]
    tag = "/".join(["root" if root else "----", "succ" if succ else "----", "tail" if tail else "----"])
    if root and succ and tail and not a.endswith("+"):
        return "PASS(full)", tag
    return "FAIL", tag

FAIL_CODE_RE = re.compile(r"^\d+/\d+$")

def parse_fail_code(value):
    if not FAIL_CODE_RE.fullmatch(value):
        raise argparse.ArgumentTypeError("fail code must be CLASS/CODE, for example 1/99")
    return value

def debug_value(value):
    if isinstance(value, str):
        return value
    return str(value)

def labels_from_json(path, fail_code=None):
    try:
        with open(path, encoding="utf-8") as jf:
            records = json.load(jf)
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read JSON result file {path}: {exc}") from exc
    if not isinstance(records, list):
        raise ValueError(f"JSON result file {path} must contain a list")
    labels = []
    for number, record in enumerate(records, 1):
        if not isinstance(record, dict) or not isinstance(record.get("label"), str):
            raise ValueError(f"JSON result {path} entry {number} has no label")
        if fail_code is not None:
            is_failure = str(record.get("class", "")).startswith("FAIL")
            if not is_failure or debug_value(record.get("dbg", -1)) != fail_code:
                continue
        labels.append(record["label"])
    return labels

def labels_from_file(path):
    try:
        with open(path, encoding="utf-8") as lf:
            return [line.strip() for line in lf
                    if line.strip() and not line.lstrip().startswith("#")]
    except OSError as exc:
        raise ValueError(f"cannot read label file {path}: {exc}") from exc

def select_labels(rows, labels):
    by_label = {}
    for row in rows:
        if row:
            by_label.setdefault(row[0], row)
    missing = [label for label in labels if label not in by_label]
    if missing:
        shown = ", ".join(missing[:5])
        if len(missing) > 5:
            shown += ", ..."
        raise ValueError(f"labels not found in manifest: {shown}")
    return [by_label[label] for label in labels]

def print_failure_histogram(results):
    histogram = Counter(
        (r.get("regions", ""), debug_value(r.get("dbg", -1)))
        for r in results
        if str(r.get("class", "")).startswith("FAIL")
    )
    if not histogram:
        return
    print(" failure histogram (regions, fail):")
    for (regions, fail), count in sorted(
            histogram.items(), key=lambda item: (-item[1], item[0])):
        print(f"  ({regions or '-'}, {fail}) = {count}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("elf"); ap.add_argument("manifest")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--skip", type=int, default=0)
    ap.add_argument("--filter", default="")
    ap.add_argument("--out-dir", default=os.path.join(ROOT, "work/run"))
    ap.add_argument("--quiet-passes", action="store_true")
    ap.add_argument("--ziskemu", action="store_true")
    ap.add_argument("--json", default="")
    selection = ap.add_mutually_exclusive_group()
    selection.add_argument("--from-json", default="", metavar="FILE",
                           help="select labels from a previous --json result file")
    selection.add_argument("--labels", default="", metavar="FILE",
                           help="run labels listed one per line in FILE")
    ap.add_argument("--fail-code", default=None, type=parse_fail_code,
                    metavar="CLASS/CODE",
                    help="with --from-json, rerun only matching failing codes")
    a = ap.parse_args()
    if a.fail_code is not None and not a.from_json:
        ap.error("--fail-code requires --from-json")
    manifest_path = os.path.abspath(a.manifest)
    manifest_dir = os.path.dirname(manifest_path)
    try:
        with open(manifest_path) as manifest:
            rows = [l.rstrip("\n").split("\t") for l in manifest if l.strip()]
        if a.from_json:
            rows = select_labels(rows, labels_from_json(a.from_json, a.fail_code))
        elif a.labels:
            rows = select_labels(rows, labels_from_file(a.labels))
    except (OSError, ValueError) as exc:
        ap.error(str(exc))
    if a.filter: rows = [r for r in rows if a.filter in r[0] or (len(r) > 6 and a.filter in r[6])]
    rows = rows[a.skip:]
    if a.limit: rows = rows[:a.limit]
    missing = []
    for row in rows:
        row[1] = resolve_input_path(row[1], manifest_dir)
        if not os.path.isfile(row[1]):
            missing.append((row[0], row[1]))
    if missing:
        for label, path in missing:
            print(f"error: input file not found for {label}: {path}", file=sys.stderr)
        return 2
    os.makedirs(a.out_dir, exist_ok=True)
    with ThreadPoolExecutor(a.jobs) as ex:
        results = list(ex.map(lambda r: run_case(a.elf, r, a.out_dir, a.ziskemu), rows))
    counts = {}
    steps_pass = []
    for r in results:
        cls, tag = classify(r)
        counts[cls] = counts.get(cls, 0) + 1
        if cls.startswith("PASS") and r["steps"] is not None: steps_pass.append(r["steps"])
        r["class"] = cls; r["regions"] = tag
        if cls.startswith("PASS") and a.quiet_passes: continue
        line = f"  {cls:16s} {tag:16s} fail={r['dbg']:<6} steps={r['steps']} {r['secs']:.2f}s {r['label'][:80]}"
        print(line)
        if cls.startswith("FAIL"):
            print(f"    expected: {r['expected']}\n    actual:   {r['actual']}")
    print("=" * 60)
    print(f" total: {len(results)}  " + "  ".join(f"{k}: {v}" for k, v in sorted(counts.items())))
    if steps_pass:
        print(f" steps over passing cases: min={min(steps_pass)} max={max(steps_pass)} "
              f"mean={sum(steps_pass)//len(steps_pass)}")
    print_failure_histogram(results)
    if a.json:
        json.dump(results, open(a.json, "w"), indent=1)
    return 0 if all(r["class"].startswith("PASS") for r in results) else 1

if __name__ == "__main__":
    sys.exit(main())
