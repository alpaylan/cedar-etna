#!/usr/bin/env bash
# Validate the cedar-lean ETNA workload end-to-end.
#
# Contract enforced (mirrors etna-ify/skills/validate/SKILL.md, Lean variant):
#   1. `lake build etna_cedar` succeeds on base.
#   2. For each `[[tasks]]` block in etna.toml whose `tasks.injection.kind = "patch"`:
#        a. Reverse-apply the patch -> buggy state.
#        b. `lake build etna_cedar` succeeds (runner closure must still typecheck).
#        c. `lake exe etna_cedar etna <Property>` returns status:"failed".
#        d. Forward-apply patch -> restore base; same runner returns status:"passed".
#
# Build target note: we use `lake build etna_cedar` rather than `lake build Cedar`
# so that variants whose buggy state breaks the *proofs* in `Cedar/Thm/` (load-bearing
# soundness theorems coupled to the validator implementation) can still be exercised
# at runtime. The implementation closure reachable from `EtnaCedar.Main` is what
# the runner actually executes.
#
# Usage: scripts/validate_lean_workload.sh [workload-dir]
# Default workload dir: parent of this script.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKLOAD_DIR="${1:-$(dirname "$SCRIPT_DIR")}"

# Two supported layouts:
#   Local dev tree:  $WORKLOAD_DIR/.cedar-spec/cedar-lean/  (etnaify_cedar.sh bootstrap)
#   Forked repo:     $WORKLOAD_DIR/cedar-lean/             (alpaylan/cedar-etna fork)
if [ -d "$WORKLOAD_DIR/.cedar-spec/cedar-lean" ]; then
  SPEC_DIR="$WORKLOAD_DIR/.cedar-spec"
  LEAN_DIR="$SPEC_DIR/cedar-lean"
elif [ -d "$WORKLOAD_DIR/cedar-lean" ]; then
  SPEC_DIR="$WORKLOAD_DIR"
  LEAN_DIR="$WORKLOAD_DIR/cedar-lean"
else
  echo "[validate] error: neither $WORKLOAD_DIR/.cedar-spec/cedar-lean nor $WORKLOAD_DIR/cedar-lean exists" >&2
  exit 1
fi

ETNA_TOML="$WORKLOAD_DIR/etna.toml"

cd "$LEAN_DIR"

echo "[validate] base build…"
lake build etna_cedar 1>/dev/null
echo "[validate] base build ok"

# Parse [[tasks]] blocks: extract (mutation, property, patch) triples.
python3 - "$ETNA_TOML" <<'PY' > /tmp/etna_tasks.tsv
import sys, re, tomllib
with open(sys.argv[1], "rb") as f:
    data = tomllib.load(f)
for t in data.get("tasks", []):
    mutation = t["mutations"][0]
    patch = t["injection"]["patch"]
    prop = t["tasks"][0]["property"]
    print(f"{mutation}\t{prop}\t{patch}")
PY

while IFS=$'\t' read -r mutation prop patch; do
  patchfile="$WORKLOAD_DIR/$patch"
  echo
  echo "[validate] === variant: $mutation ==="

  # base -> buggy
  echo "[validate]   reverse-apply $patch …"
  ( cd "$SPEC_DIR" && git apply -R --whitespace=nowarn "$patchfile" )

  echo "[validate]   build buggy state …"
  lake build etna_cedar 1>/dev/null

  echo "[validate]   run etna witness on buggy state …"
  out=$(lake exe etna_cedar etna "$prop")
  echo "$out"
  status=$(python3 -c "import json,sys;print(json.loads(sys.argv[1])['status'])" "$out")
  if [ "$status" != "failed" ]; then
    echo "[validate] FAIL: witness must report status=failed on buggy state, got '$status'"
    ( cd "$SPEC_DIR" && git apply --whitespace=nowarn "$patchfile" ) || true
    exit 1
  fi

  # buggy -> base
  echo "[validate]   forward-apply $patch (restore base) …"
  ( cd "$SPEC_DIR" && git apply --whitespace=nowarn "$patchfile" )

  echo "[validate]   run etna witness on restored base …"
  out=$(lake exe etna_cedar etna "$prop")
  echo "$out"
  status=$(python3 -c "import json,sys;print(json.loads(sys.argv[1])['status'])" "$out")
  if [ "$status" != "passed" ]; then
    echo "[validate] FAIL: witness must report status=passed on restored base, got '$status'"
    exit 1
  fi
  echo "[validate]   variant ok"
done < /tmp/etna_tasks.tsv

echo
echo "[validate] all $(wc -l < /tmp/etna_tasks.tsv | tr -d ' ') variant(s) ok"
