#!/usr/bin/env bash
# Replay all 25 modules of the proof of R(12,12) >= 1661 through leanchecker, one module per
# run, plus a control.  leanchecker replays the modules it is given in parallel, and each
# H01Branch module and R1661.Checks need 4-8 GB, so they are taken one at a time.
set -uo pipefail
cd "$(dirname "$0")/.."
LOG=audit/logs_1661
mkdir -p "$LOG"
# the import closure of RamseyIncrement.R1661.Main
# (the modules that need more than 4 GB first)
modules=(
  R1212.H01Branch0 R1212.H01Branch1 R1212.H01Branch2 R1212.H01Branch3
  R1212.H01Branch4 R1212.H01Branch5 R1212.H01Branch6 R1212.H01Branch7
  R1661.Checks
  Basic SpecialLift Cone
  R1212.Search R1212.H01Data
  R1212.H01NoK8 R1212.Paley R1212.Mathon R1212.PaleyClique
  R1658.Defect
  R1661.Data R1661.Graph R1661.Projection
  Transport RamseyNumber R1661.Main
)
status=0
: > "$LOG/leanchecker.tsv"
printf 'module\texit\tseconds\tpeak_GB\tolean_sha256\n' >> "$LOG/leanchecker.tsv"
for m in "${modules[@]}"; do
  t0=$(date +%s)
  nice -n 10 /usr/bin/time -l lake env leanchecker "RamseyIncrement.$m" \
    > "$LOG/lc_$m.out" 2> "$LOG/lc_$m.err"
  rc=$?
  peak=$(awk '/maximum resident set size/ {printf "%.2f", $1 / 1073741824}' "$LOG/lc_$m.err")
  sha=$(shasum -a 256 ".lake/build/lib/lean/RamseyIncrement/$(echo "$m" | tr . /).olean" 2>/dev/null | cut -d' ' -f1)
  sha=${sha:-missing}
  printf '%s\t%s\t%s\t%s\t%s\n' "RamseyIncrement.$m" "$rc" "$(( $(date +%s) - t0 ))" "$peak" "$sha" \
    >> "$LOG/leanchecker.tsv"
  if [ "$rc" -eq 0 ]; then echo "ok    RamseyIncrement.$m (${peak} GB)"; else echo "FAIL  RamseyIncrement.$m"; status=1; fi
done
# Control: a module that does not exist must be rejected.
if lake env leanchecker RamseyIncrement.R1661.NoSuchModule > /dev/null 2>&1; then
  echo "FAIL  control: a missing module was accepted"
  status=1
else
  echo "ok    control: a missing module is rejected"
fi
exit $status
