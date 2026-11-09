#!/usr/bin/env bash
# Build the Lean proof of R(12,12) >= 1661, one module at a time, and print the axioms.
#
# The published modules (RamseyNumber, Basic, Transport, R1212/*, R1658/Defect, ...) are
# unchanged. From a fresh clone the script first downloads the Mathlib cache and builds the
# eight H01Branch modules one at a time (4-7 GB each), as build_r1658.sh of r1212-1658 does.
# (Our run started from the .lake of the r1212-1658 build, so these modules were replayed.)
# R1661.Checks needs about 6-7 GB in the Lean kernel, so `lake build` is never asked to
# compile two new modules at once.
#
# The logs go to $LOG, by default audit/logs_local/ (ignored by git); the records of our runs
# are in audit/logs_1661/ and audit/logs_fresh_build/. Each step is timed, and its peak memory
# is recorded where /usr/bin/time exists (see audit/portable.sh).
set -uo pipefail
cd "$(dirname "$0")/.."
. audit/portable.sh
LOG=${LOG:-audit/logs_local}
mkdir -p "$LOG"
step() {
  local name=$1; shift
  echo "== [$(date '+%F %T')] $name: $*"
  local t0=$(date +%s)
  run_measured "$LOG/$name.out" "$LOG/$name.err" "$@"
  local rc=$?
  echo "== [$(date '+%F %T')] $name rc=$rc seconds=$(( $(date +%s) - t0 )) peak_GB=$(peak_gb "$LOG/$name.err")"
  tail -n 5 "$LOG/$name.out"
  return $rc
}
step cache_get lake exe cache get || exit 1
for i in 0 1 2 3 4 5 6 7; do
  step "build_R1212.H01Branch$i" lake build "RamseyIncrement.R1212.H01Branch$i" || exit 1
done
for m in Data Checks Graph Projection Main; do
  step "build_R1661.$m" lake build "RamseyIncrement.R1661.$m" || exit 1
done
step build_default lake build || exit 1
step axioms lake env lean AxiomAudit1661.lean || exit 1
cat "$LOG/axioms.out"
echo "== end $(date '+%F %T %Z')"
