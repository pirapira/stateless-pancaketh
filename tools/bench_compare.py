#!/usr/bin/env python3
"""Compare two JSON snapshots produced by tools/bench.py."""
import argparse
import json
import sys


METRICS = ("spike_instr", "zisk_steps", "zisk_cost")


def parse_threshold(value):
    text = value.strip()
    if text.endswith("%"):
        text = text[:-1].strip()
    try:
        threshold = float(text)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            f"invalid percentage threshold: {value!r}") from exc
    if threshold < 0:
        raise argparse.ArgumentTypeError("regression threshold must be non-negative")
    return threshold


def load_snapshot(path):
    try:
        with open(path) as source:
            data = json.load(source)
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read {path}: {exc}") from exc
    if not isinstance(data, dict) or not isinstance(data.get("fixtures"), list):
        raise ValueError(f"{path} must contain a JSON object with a fixtures list")

    fixtures = {}
    for index, fixture in enumerate(data["fixtures"]):
        if not isinstance(fixture, dict) or not isinstance(fixture.get("label"), str):
            raise ValueError(f"{path} fixture {index} has no string label")
        label = fixture["label"]
        if label in fixtures:
            raise ValueError(f"{path} contains duplicate fixture {label!r}")
        if not isinstance(fixture.get("ok"), bool):
            raise ValueError(f"{path} fixture {label!r} has non-boolean ok")
        for metric in METRICS:
            value = fixture.get(metric)
            if not isinstance(value, int) or isinstance(value, bool):
                raise ValueError(
                    f"{path} fixture {label!r} has non-integer {metric}")
        fixtures[label] = fixture
    return data, fixtures


def total_metrics(fixtures):
    selected = [fixture for fixture in fixtures.values() if fixture["ok"]]
    return {
        "fixtures": len(fixtures),
        "ok": len(selected),
        **{metric: sum(fixture[metric] for fixture in selected)
           for metric in METRICS},
    }


def format_value(value):
    return f"{value:,}" if value >= 0 else "n/a"


def format_delta(old, new):
    if old < 0 or new < 0:
        return "n/a"
    delta = new - old
    if old == 0:
        percent = "n/a"
    else:
        percent = f"{delta * 100 / old:+.2f}%"
    return f"{delta:+,} ({percent})"


def instruction_regressed(old, new, threshold):
    if old < 0 or new < 0 or old == 0:
        return False
    return (new - old) * 100 / old > threshold


def fixture_result(label, old, new, threshold):
    if old is None:
        return "REGRESSION", [f"{label}: missing from old snapshot"]
    if new is None:
        return "REGRESSION", [f"{label}: missing from new snapshot"]

    problems = []
    improvements = []
    if old["ok"] != new["ok"]:
        if old["ok"]:
            problems.append("ok true->false")
        else:
            improvements.append("ok false->true")
    if instruction_regressed(old["spike_instr"], new["spike_instr"], threshold):
        growth = ((new["spike_instr"] - old["spike_instr"])
                  * 100 / old["spike_instr"])
        problems.append(f"spike_instr +{growth:.2f}%")
    elif (old["spike_instr"] >= 0 and new["spike_instr"] >= 0
          and new["spike_instr"] < old["spike_instr"]):
        improvements.append("spike_instr decreased")

    if problems:
        return "REGRESSION", problems
    if improvements:
        return "IMPROVED", improvements
    return "UNCHANGED", []


def main():
    ap = argparse.ArgumentParser(
        description="compare bench.py JSON snapshots and detect regressions")
    ap.add_argument("old", metavar="OLD.json")
    ap.add_argument("new", metavar="NEW.json")
    ap.add_argument("--max-regress", type=parse_threshold, default=2.0,
                    metavar="PERCENT",
                    help="maximum allowed Spike instruction growth (default: 2%%)")
    args = ap.parse_args()

    try:
        _, old_fixtures = load_snapshot(args.old)
        _, new_fixtures = load_snapshot(args.new)
    except ValueError as exc:
        print(f"bench_compare: {exc}", file=sys.stderr)
        return 2

    labels = list(old_fixtures)
    labels.extend(label for label in new_fixtures if label not in old_fixtures)
    print(f"max Spike instruction growth: {args.max_regress:.2f}%")
    print("fixture | status | spike_instr old -> new (delta) | "
          "zisk_steps old -> new (delta) | zisk_cost old -> new (delta)")
    regressions = []
    for label in labels:
        old = old_fixtures.get(label)
        new = new_fixtures.get(label)
        status, reasons = fixture_result(label, old, new, args.max_regress)
        if status == "REGRESSION":
            regressions.extend(reasons)
        if old is None or new is None:
            columns = ["n/a", "n/a", "n/a"]
        else:
            columns = [
                f"{format_value(old[metric])} -> {format_value(new[metric])} "
                f"{format_delta(old[metric], new[metric])}"
                for metric in METRICS
            ]
        print(f"{label} | {status} | " + " | ".join(columns))

    old_totals = total_metrics(old_fixtures)
    new_totals = total_metrics(new_fixtures)
    print("\ntotal | "
          f"fixtures {old_totals['fixtures']} -> {new_totals['fixtures']} "
          f"({new_totals['fixtures'] - old_totals['fixtures']:+d}) | "
          f"ok {old_totals['ok']} -> {new_totals['ok']} "
          f"{format_delta(old_totals['ok'], new_totals['ok'])} | "
          + " | ".join(
              f"{metric} {format_value(old_totals[metric])} -> "
              f"{format_value(new_totals[metric])} "
              f"{format_delta(old_totals[metric], new_totals[metric])}"
              for metric in METRICS))

    if regressions:
        print(f"\nREGRESSION: {len(regressions)}")
        for reason in regressions:
            print(f"- {reason}")
        return 1
    print("\nNo performance regressions.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
