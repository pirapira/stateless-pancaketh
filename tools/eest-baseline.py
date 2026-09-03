#!/usr/bin/env python3
"""Check and update the checked-in EEST fixture baseline.

The baseline keeps fixture labels as well as the allowed failures.  Counts
alone cannot detect a regression when one previously passing fixture fails and
another fixture improves, so labels are the source of truth and counts are
human-readable summary fields.

Usage:
  tools/eest-baseline.py check  MANIFEST.tsv RESULTS.json
  tools/eest-baseline.py update MANIFEST.tsv RESULTS.json

Use --baseline PATH before the subcommand to operate on another baseline file.
"""
import argparse
import json
import os
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE = ROOT / "tools" / "eest-baseline.json"
VERSION = 1


def manifest_name(path):
    return Path(path).resolve().parent.name


def load_json(path):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read JSON {path}: {exc}") from exc


def debug_value(value):
    if isinstance(value, str):
        return value
    return str(value)


def is_pass(record):
    return str(record.get("class", "")).startswith("PASS")


def summarize(results):
    if not isinstance(results, list):
        raise ValueError("runner JSON must contain a list")
    labels = []
    seen = set()
    failures = {}
    histogram = Counter()
    pass_count = 0
    pass_full_count = 0
    for number, record in enumerate(results, 1):
        if not isinstance(record, dict) or not isinstance(record.get("label"), str):
            raise ValueError(f"runner JSON entry {number} has no label")
        label = record["label"]
        if label in seen:
            raise ValueError(f"runner JSON contains duplicate label {label}")
        seen.add(label)
        labels.append(label)
        cls = str(record.get("class", ""))
        if is_pass(record):
            pass_count += 1
            if cls == "PASS(full)":
                pass_full_count += 1
            continue
        dbg = debug_value(record.get("dbg", -1))
        regions = str(record.get("regions", ""))
        failures[label] = {
            "class": cls,
            "dbg": dbg,
            "regions": regions,
        }
        histogram[f"{regions}, {dbg}"] += 1
    return {
        "total": len(labels),
        "pass": pass_count,
        "pass_full": pass_full_count,
        "labels": labels,
        "failures": failures,
        "failure_histogram": dict(sorted(histogram.items())),
    }


def load_baseline(path):
    if not path.exists():
        return {"version": VERSION, "manifests": {}}
    data = load_json(path)
    if not isinstance(data, dict) or data.get("version") != VERSION:
        raise ValueError(f"unsupported baseline format in {path}")
    manifests = data.get("manifests")
    if not isinstance(manifests, dict):
        raise ValueError(f"baseline {path} has no manifests object")
    return data


def write_baseline(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
    os.replace(tmp, path)


def update(path, manifest, results_path):
    data = load_baseline(path)
    name = manifest_name(manifest)
    data["manifests"][name] = summarize(load_json(results_path))
    write_baseline(path, data)
    entry = data["manifests"][name]
    print(f"updated {path}: {name} {entry['pass']}/{entry['total']} pass, "
          f"{len(entry['failures'])} allowed failures")


def check(path, manifest, results_path):
    data = load_baseline(path)
    name = manifest_name(manifest)
    entry = data["manifests"].get(name)
    if entry is None:
        print(f"EEST baseline: no entry for manifest {name}", file=sys.stderr)
        return 1
    current = summarize(load_json(results_path))
    baseline_labels = set(entry.get("labels", []))
    current_by_label = {label: label for label in current["labels"]}
    current_failures = current["failures"]
    baseline_failures = entry.get("failures", {})
    problems = []

    for label in sorted(baseline_labels - set(current_by_label)):
        problems.append(f"missing baseline fixture: {label}")

    # A label that was passing in the baseline must remain a PASS result.
    for label in sorted(baseline_labels - set(baseline_failures)):
        record = current_failures.get(label)
        if record is not None:
            problems.append(
                f"regression in previously passing fixture {label}: "
                f"{record['class']} fail={record['dbg']}"
            )

    # Failures are allowed only for the same fixture and the same failure
    # class/code recorded by update.  A new fixture failure is also new.
    for label, record in sorted(current_failures.items()):
        expected = baseline_failures.get(label)
        if expected is None:
            if label in baseline_labels:
                # A baseline-passing label was already reported above with
                # the more useful regression message.
                continue
            problems.append(
                f"new failure in {label}: {record['class']} fail={record['dbg']}"
            )
            continue
        if (record.get("class"), record.get("dbg")) != (
                expected.get("class"), debug_value(expected.get("dbg", -1))):
            problems.append(
                f"changed failure code in {label}: "
                f"baseline {expected.get('class')} fail={expected.get('dbg')}; "
                f"current {record['class']} fail={record['dbg']}"
            )

    if problems:
        print(f"EEST baseline {name}: FAIL", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    improved = sorted(set(baseline_failures) - set(current_failures))
    if improved:
        print(f"EEST baseline {name}: PASS (strictly better; "
              f"{len(improved)} allowed failures cleared)")
        print(f"  refresh with: python3 tools/eest-baseline.py update "
              f"{manifest} {results_path}")
    else:
        print(f"EEST baseline {name}: PASS "
              f"({current['pass']}/{current['total']} pass, "
              f"{len(current_failures)} allowed failures)")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--baseline", default=str(DEFAULT_BASELINE),
                    help="baseline JSON path (default: tools/eest-baseline.json)")
    sub = ap.add_subparsers(dest="command", required=True)
    for command in ("check", "update"):
        p = sub.add_parser(command)
        p.add_argument("manifest")
        p.add_argument("results_json")
    args = ap.parse_args()
    try:
        if args.command == "check":
            return check(Path(args.baseline), args.manifest, args.results_json)
        update(Path(args.baseline), args.manifest, args.results_json)
        return 0
    except ValueError as exc:
        print(f"eest-baseline: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
