#!/usr/bin/env python3
"""
Manual experiment driver for the cedar-etna workload.

`etna experiment run` does not yet apply `injection.kind = "patch"` variants
(it only supports marauders), so until that lands in etna-cli's driver this
script does the equivalent work directly:

  - read etna.toml's [[tasks]]
  - for each (task, strategy, trial):
      * `git apply -R` the variant's patch into .cedar-spec / cedar-lean
      * `lake build etna_cedar`
      * `lake exe etna_cedar <strategy> <property>` and capture JSON
      * `git apply` to restore
      * append a Metric-shaped row to store.jsonl

Output `store.jsonl` matches the schema etna-cli's `etna analyze` and
`etna experiment report` consume (see CANONICAL_ORDER in
alpaylan/etna-cli:src/store.rs), so downstream visualisation works.

Usage (run from the workload root):
  python3 scripts/run_etna_experiment.py \\
      --strategy plausible \\
      --trials 10 \\
      --timeout 60 \\
      --experiment cedar-etna-demo \\
      --store store.jsonl
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import subprocess
import sys
import time
import tomllib
from pathlib import Path


def detect_layout(workload_dir: Path) -> tuple[Path, Path]:
    """Return (spec_dir, lean_dir) supporting both layouts."""
    if (workload_dir / ".cedar-spec" / "cedar-lean").is_dir():
        spec = workload_dir / ".cedar-spec"
        return spec, spec / "cedar-lean"
    if (workload_dir / "cedar-lean").is_dir():
        return workload_dir, workload_dir / "cedar-lean"
    raise SystemExit(f"[error] no cedar-lean/ found under {workload_dir}")


def run(cmd: list[str], cwd: Path, capture: bool = False) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, check=True,
                          capture_output=capture, text=capture)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawTextHelpFormatter)
    p.add_argument("--workload-dir", default=str(Path(__file__).resolve().parent.parent),
                   help="Workload root (default: parent of this script's dir)")
    p.add_argument("--strategy", default="plausible",
                   choices=["etna", "plausible"],
                   help="Tool to invoke (default: plausible)")
    p.add_argument("--trials", type=int, default=10,
                   help="Trials per (variant, property)")
    p.add_argument("--timeout", type=float, default=60.0,
                   help="Per-trial timeout in seconds (etna timeout, not enforced here)")
    p.add_argument("--experiment", default="cedar-etna",
                   help="Experiment name to record")
    p.add_argument("--store", default=None,
                   help="Output JSONL path (default: <workload>/store.jsonl)")
    p.add_argument("--mutations", default=None,
                   help="Comma-separated list of mutation names (default: all)")
    p.add_argument("--properties", default=None,
                   help="Comma-separated list of property names (default: all)")
    args = p.parse_args()

    workload = Path(args.workload_dir).resolve()
    spec, lean = detect_layout(workload)
    store_path = Path(args.store) if args.store else workload / "store.jsonl"
    etna_toml = workload / "etna.toml"

    with etna_toml.open("rb") as f:
        manifest = tomllib.load(f)

    print(f"[run] workload    : {workload}")
    print(f"[run] spec/lean   : {spec} / {lean}")
    print(f"[run] strategy    : {args.strategy}")
    print(f"[run] trials      : {args.trials}")
    print(f"[run] store       : {store_path}")

    print(f"[run] base build (lake build etna_cedar) …")
    run(["lake", "build", "etna_cedar"], cwd=lean)

    selected_mutations = set(args.mutations.split(",")) if args.mutations else None
    selected_properties = set(args.properties.split(",")) if args.properties else None

    rows: list[dict] = []
    for task in manifest["tasks"]:
        mutation = task["mutations"][0]
        if selected_mutations and mutation not in selected_mutations:
            continue
        for sub in task["tasks"]:
            prop = sub["property"]
            if selected_properties and prop not in selected_properties:
                continue
            patch = workload / task["injection"]["patch"]
            print(f"\n[run] === {mutation} / {prop} ({args.strategy}) ===")
            print(f"[run]   reverse-apply {patch.name}")
            run(["git", "apply", "-R", "--whitespace=nowarn", str(patch)], cwd=spec)
            try:
                run(["lake", "build", "etna_cedar"], cwd=lean)
                for trial in range(1, args.trials + 1):
                    t0 = time.monotonic()
                    cp = run(["lake", "exe", "etna_cedar", args.strategy, prop],
                             cwd=lean, capture=True)
                    elapsed_ms = (time.monotonic() - t0) * 1000.0
                    line = next(l for l in cp.stdout.strip().splitlines()
                                if l.startswith("{"))
                    payload = json.loads(line)
                    row = {
                        "experiment": args.experiment,
                        "workload": manifest["name"],
                        "language": manifest["language"],
                        "strategy": args.strategy,
                        "property": prop,
                        "mutations": [mutation],
                        "mode": "solve",
                        "trial": trial,
                        "timeout": args.timeout,
                        "timestamp": _dt.datetime.utcnow().isoformat() + "Z",
                        "status": payload.get("status"),
                        "tests": payload.get("tests"),
                        "discards": payload.get("discards", 0),
                        "time": payload.get("time"),
                        "wall_ms": round(elapsed_ms, 3),
                    }
                    if payload.get("counterexample") is not None:
                        row["counterexample"] = payload["counterexample"]
                    if payload.get("error") is not None:
                        row["error"] = payload["error"]
                    rows.append(row)
                    print(f"[run]   trial {trial:>3}/{args.trials}: "
                          f"{row['status']:8} tests={row['tests']:>6} "
                          f"wall={row['wall_ms']:.0f}ms")
            finally:
                print(f"[run]   forward-apply (restore base)")
                run(["git", "apply", "--whitespace=nowarn", str(patch)], cwd=spec)

    print(f"\n[run] writing {len(rows)} rows to {store_path}")
    with store_path.open("a") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    print("[run] done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
