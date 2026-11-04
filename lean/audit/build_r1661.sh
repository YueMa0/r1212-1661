#!/usr/bin/env bash
# Build the Lean proof of R(12,12) >= 1661, one module at a time, and print the axioms.
#
# The published modules (RamseyNumber, Basic, Transport, R1212/*, R1658/Defect, ...) are
# unchanged. From a fresh clone the script first downloads the Mathlib cache and builds the
# eight H01Branch modules one at a time (4-7 GB each), as build_r1658.sh of r1212-1658 does.
# (Our run started from the .lake of the r1212-1658 build, so these modules were replayed.)
# R1661.Checks needs up to about 8 GB in the Lean kernel, so `lake build` is never asked to
# compile two new modules at once.  Each step is timed (/usr/bin/time -l: peak memory).
set -uo pipefail
cd "$(dirname "$0")/.."
LOG=audit/logs_1661
mkdir -p "$LOG"
step() {
  local name=$1; shift
  echo "== [$(date '+%F %T')] $name: $*"
  local t0=$(date +%s)
  nice -n 10 /usr/bin/time -l "$@" > "$LOG/$name.out" 2> "$LOG/$name.err"
  local rc=$?
  local peak=$(awk '/maximum resident set size/ {printf "%.2f", $1 / 1073741824}' "$LOG/$name.err")
  echo "== [$(date '+%F %T')] $name rc=$rc seconds=$(( $(date +%s) - t0 )) peak_GB=$peak"
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
