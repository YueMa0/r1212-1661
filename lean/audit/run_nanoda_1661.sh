#!/bin/bash
# nanoda (independent Lean 4 kernel, Rust) on R(12,12) >= 1661: the full theorem, plus a control
# whose export has one bit of a table changed and must be rejected.
# usage: LEAN4EXPORT=/path/to/lean4export NANODA=/path/to/nanoda_bin audit/run_nanoda_1661.sh
# Versions used for audit/logs_1661/nanoda/: nanoda_lib commit d0a02cc and lean4export v4.32.2
# (toolchain set to v4.32.1), the same as for r1212-1642 and r1212-1658. macOS (/usr/bin/time -l).
# Peak memory of the full run for R1658 was about 10 GB (27 minutes, one thread).
cd "$(dirname "$0")/.." || exit 2
N=audit/logs_1661/nanoda
mkdir -p "$N"
exec > >(tee -a "$N/nanoda.log") 2>&1
: "${LEAN4EXPORT:?set LEAN4EXPORT to the lean4export binary}"
: "${NANODA:?set NANODA to the nanoda_bin binary}"
PY=${PY:-python3}
echo "nanoda_bin sha256 $(shasum -a 256 "$NANODA" | cut -d' ' -f1)"
echo "lean4export sha256 $(shasum -a 256 "$LEAN4EXPORT" | cut -d' ' -f1)"
cfg() {  # cfg NAME EXPORT DECL
  cat > "$N/$1.json" <<EOF
{"export_file_path": "$2", "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
 "unpermitted_axiom_hard_error": true, "unknown_pp_declar_hard_error": true,
 "nat_extension": true, "string_extension": true, "num_threads": 1,
 "pp_declars": [$3], "pp_to_stdout": true, "print_success_message": true}
EOF
}
echo "== [$(date '+%T')] export the full theorem"
lake env "$LEAN4EXPORT" RamseyIncrement.R1661.Main -- RamseyIncrement.R1661.r1212_lower_bound > "$N/full.ndjson"
echo "export rc=$? bytes=$(wc -c < "$N/full.ndjson") sha256 $(shasum -a 256 "$N/full.ndjson" | cut -d' ' -f1)"
cfg full "$N/full.ndjson" '"RamseyIncrement.R1661.r1212_lower_bound", "RamseyIncrement.ramseyNumber", "RamseyIncrement.ForcesRamsey", "RamseyIncrement.HasRamseyColoring", "RamseyIncrement.IsRamseyFree", "SimpleGraph.CliqueFree", "SimpleGraph.IsNClique", "SimpleGraph.IsClique"'
echo "== [$(date '+%T')] nanoda: full theorem"
nice -n 10 /usr/bin/time -l "$NANODA" "$N/full.json" > "$N/full.out" 2> "$N/full.err"
echo "nanoda full exit=$? peak_GB=$(awk '/maximum resident set size/ {printf "%.2f", $1 / 1073741824}' "$N/full.err")"
cat "$N/full.out"; grep -v -E '^ +[0-9]+ ' "$N/full.err" | head -5
echo "== [$(date '+%T')] control: badRow_spec as exported, then with one bit of badRLit flipped"
lake env "$LEAN4EXPORT" RamseyIncrement.R1661.Checks -- RamseyIncrement.R1661.badRow_spec > "$N/ctrl.ndjson"
BAD=$($PY -c "import re;print(int(re.search(r'def badRLit : ℕ := 0x([0-9a-f]+)', open('RamseyIncrement/R1661/Data.lean').read()).group(1), 16))")
$PY - "$N/ctrl.ndjson" "$N/ctrl_tampered.ndjson" "$BAD" <<'PY'
import sys
src, dst, bad = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(src).read().split('\n')
hits = [i for i, l in enumerate(lines) if l.endswith('"natVal":"%s"}' % bad)]
print('lines holding badRLit:', hits)
assert len(hits) == 1
lines[hits[0]] = lines[hits[0]].replace('"%s"' % bad, '"%d"' % (int(bad) ^ 32))
open(dst, 'w').write('\n'.join(lines))
PY
cfg ctrl "$N/ctrl.ndjson" '"RamseyIncrement.R1661.badRow_spec"'
cfg ctrl_tampered "$N/ctrl_tampered.ndjson" '"RamseyIncrement.R1661.badRow_spec"'
"$NANODA" "$N/ctrl.json" > "$N/ctrl.out" 2>&1; echo "control as exported: exit=$? (must be 0)"; tail -2 "$N/ctrl.out"
"$NANODA" "$N/ctrl_tampered.json" > "$N/ctrl_tampered.out" 2>&1; echo "control tampered: exit=$? (must be nonzero)"; tail -3 "$N/ctrl_tampered.out"
echo "== [$(date '+%T')] nanoda done"
