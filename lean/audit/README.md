# Building and auditing the Lean proof

All commands are run from lean/.

| File | Purpose |
|---|---|
| build_r1661.sh | fetch the Mathlib cache, build the eight H01Branch modules and the five new modules one at a time, build the default target, print the axioms |
| leanchecker_r1661.sh | leanchecker replay of all 25 modules, one per run, plus a control |
| run_nanoda_1661.sh | the check with nanoda, an independent kernel, and its control |
| portable.sh | helpers that the three scripts share: SHA-256 and peak memory on each system |
| sources_1661.sha256 | SHA-256 of the Lean sources, entry points, helper scripts and build files in lean/ |
| logs_1661/ | the records of our runs |
| logs_fresh_build/ | the records of a second build, from scratch |
| logs_local/ | where new runs of the scripts write their logs (set LOG to change it); git ignores it |

The default target, RamseyIncrement.lean, imports only RamseyIncrement.R1661.Main. So `lake build` compiles the 25 modules that the theorem needs: the 5 new modules in RamseyIncrement/R1661/, RamseyIncrement/R1658/Defect.lean from r1212-1658, and 19 modules of r1212-1642 v1.0.0, all unchanged (see UPSTREAM.md at the top of the repository).

The scripts need bash 3.2 or later and run on macOS and Linux. portable.sh holds what differs between these systems: the SHA-256 program, and /usr/bin/time for the peak memory of each step (BSD time -l on macOS, GNU time -v on Linux; without it the scripts still run and record n/a). Our runs were made on macOS with the scripts of version 1.0.0, which called `/usr/bin/time -l` and `shasum` directly and wrote into logs_1661/; the scripts now write into logs_local/, so that the records below stay as they are.

## What Lean checks, and what it does not

- **Lean.** `RamseyIncrement.R1661.r1212_lower_bound : 1661 ≤ ramseyNumber 12 12`.
  - The finite checks on the 85 core vertices (`noK12`, `checks_ok`, and the lemmas that tie the lookup tables to their definitions, such as `badRow_spec` and `cstMask_spec`) are evaluated by the Lean kernel with `decide +kernel`, so they are part of the proof.
  - The proof uses three facts about M(797): that it is an (11,11)-colouring (`mathon_isRamseyFree` and `paley_cliqueFree` from r1212-1642); that antipodal vertices have opposite colours to every other vertex (`mathon_antip`, proved from −1 being a square mod 797); and its colours on the 21 vertices of Σ_V (`sigR_spec`, `antiRow_spec`, by kernel computation).
  - It reuses `defect_le_one` from r1212-1658 and Tatarevic's definition of `ramseyNumber`.
- **Not Lean: that the colouring defined in Lean is graph/r1212_1660.graph.**
  - gen/gen_data_1661.py generates the tables in RamseyIncrement/R1661/Data.lean from the file. It also checks the SHA-256 of the file, that V° carries M(797), and that every core vertex has a unique type.
  - tools/compare_export_1661.py rebuilds all 1660 × 1660 colours from Data.lean, following the definitions in Graph.lean, and compares them with the file.
  - Export1661.lean has Lean's interpreter evaluate the 85 core rows of `G1660.Adj` directly.
  - The theorem does not depend on these comparisons.

```bash
python3 gen/gen_data_1661.py ../graph/r1212_1660.graph --out /tmp/Data.lean
cmp /tmp/Data.lean RamseyIncrement/R1661/Data.lean
mkdir -p build/export && cp audit/logs_1661/rows_1661_from_lean.txt build/export/
python3 tools/compare_export_1661.py ../graph/r1212_1660.graph
```

- The third command lets compare_export_1661.py also compare the 85 rows recorded from Lean's interpreter; without it, the script compares only the rebuild from Data.lean.
- The header of Data.lean names the colouring b1660_PM2.graph, the name the file had when the proof was built. It is the same file as graph/r1212_1660.graph, with the same SHA-256, which gen_data_1661.py checks.
- gen_data_1661.py also runs the finite checks in Python, with the same algorithms, as a preliminary check; the proof does not use it.
- The quick-check workflow runs these commands and checks sources_1661.sha256; it does not run Lean.

## Memory

| Step | Peak memory |
|---|---|
| each H01Branch module, to compile or replay | 4–7 GB |
| R1661.Checks: compile / replay | 6.0–6.6 GB / 6.3 GB |
| nanoda, complete check | 8.4 GB |

Lake compiles independent modules in parallel, and leanchecker replays the modules it is given in parallel, so the scripts take the large modules one at a time.

## Logs (logs_1661/)

These are from runs on 3 November 2026 on an Apple M4 Mac mini with 16 GB of memory, with Lean 4.32.1 and the Mathlib revision in lake-manifest.json.

Our run started from the .lake of our build of r1212-1658. So the 20 modules that come from r1212-1642 and r1212-1658 were not recompiled. Their .olean files are byte-identical to that build (olean_vs_published.tsv), and all 25 modules were replayed by leanchecker.

The logs are as the runs wrote them, except that in gen_regen.log, gen_control_\*.log and gen_summary.json the temporary directory the generator wrote into is shown as /tmp/.

| Log | Contents |
|---|---|
| build_R1661.\*.out/.err, build_default.\* | the five new modules, compiled one at a time: Data 5 s and 1.2 GB, Checks 78 s and 6.0 GB, Graph 11 s and 2.9 GB, Projection 4 s and 2.6 GB, Main 4 s and 2.7 GB; no errors. The only warnings are the linter warnings of the unchanged modules Cone and R1212.Search, which lake repeats when it replays them (see below) |
| axioms.out | output of AxiomAudit1661.lean: the final theorem depends only on propext, Classical.choice and Quot.sound; `noK12`, `checks_ok`, `badRow_spec` and `cstMask_spec` only on propext. It also prints the statement with all implicit arguments, the definitions it uses, and a restatement in Mathlib's terms (a graph on Fin 1660 such that neither it nor its complement contains a 12-clique) |
| leanchecker_with_sha.tsv, leanchecker_run.log | leanchecker replay of the 25 modules, one per run: all exit 0, with time, peak memory and the SHA-256 of each .olean. The control, a module that does not exist, is rejected. In our run the script had a wrong path to the .olean files, so their SHA-256 were computed after the replay, from the same files (they were last written before the replay began); the script has been corrected, and now writes them into leanchecker.tsv |
| olean_vs_published.tsv | for each .olean: same as our build of r1212-1658 on this machine, and whether it equals the hash recorded for the Windows build in r1212-1658 |
| compare_export_1661.json | output of tools/compare_export_1661.py: all 2,755,600 entries rebuilt from Data.lean equal the file, and so do the 85 rows that Lean's interpreter evaluated |
| rows_1661_from_lean.txt, export.log, export.err | the 85 core rows written by Export1661.lean, run with `lake env lean Export1661.lean` (1191 s, 2.7 GB) |
| gen_\*.log, gen_summary.json | regeneration of Data.lean (identical to the file in RamseyIncrement/R1661/) and the Python preliminary check, with two negative controls: without the antipodal rule, and with the edge 1615–1616 flipped |
| nanoda/ | the check with nanoda, below |

## A build from scratch (logs_fresh_build/)

On 4 November 2026 we copied lean/ of this repository into an empty directory, without any build output, and ran `bash audit/build_r1661.sh` there, on the same Apple M4 Mac mini. build_fresh.log is its output; the other files are the logs the script wrote.

- Every step exited 0. The whole build took 14.5 minutes: 71 s for `lake exe cache get`, which found the Mathlib cache already on the computer and only decompressed it (cache_get.out), 72–114 s for each H01Branch module (at most 6.6 GB), and 38 s and 6.6 GB for R1661.Checks. On a computer without the cache, downloading it takes longer.
- axioms.out is byte-identical to logs_1661/axioms.out.
- 23 of the 25 .olean files are byte-identical to those of our first build (olean_vs_audited.tsv), including all five modules of R1661/. The other two, Cone and R1212.Search, differ by 8 bytes each; their sources are unchanged, and leanchecker accepts both (leanchecker_\*.out).
- Compiling R1212/Search.lean and Cone.lean prints linter warnings: two simp arguments are unused, and `simp at` is suggested instead of `simpa using`. They are warnings, not errors, and both files are unchanged from r1212-1642.
- olean_vs_published.tsv, olean_vs_audited.tsv and leanchecker_\*.out come from hash comparisons and single leanchecker runs made by hand, not from the scripts.

## nanoda

[nanoda](https://github.com/ammkrn/nanoda_lib) is a type checker for Lean 4 written independently of Lean, in Rust. run_nanoda_1661.sh exports `RamseyIncrement.R1661.r1212_lower_bound` with lean4export and checks it together with every declaration it uses, Mathlib included.

```bash
LEAN4EXPORT=/path/to/lean4export NANODA=/path/to/nanoda_bin audit/run_nanoda_1661.sh
```

The versions are the same as for r1212-1642 and r1212-1658: lean4export tag v4.32.2 with its lean-toolchain set to v4.32.1, and nanoda_lib commit d0a02cc. The configurations (logs_1661/nanoda/\*.json) turn on nanoda's Nat and String extensions and permit only propext, Classical.choice and Quot.sound; any other axiom is an error.

| Check | Declarations | Result | Time | Peak memory |
|---|---:|---|---:|---:|
| **r1212_lower_bound, complete** | **29,313** | **no errors** | 707 s | 8.4 GB |
| control: `badRow_spec` as exported | 694 | no errors | | |
| control: the same export with one bit of `badRLit` changed | — | **rejected**: `assertion failed: self.def_eq(u, v)`, exit code 101 | | |

- full.out prints the statement as `LE.le (OfNat.ofNat 1661) (RamseyIncrement.ramseyNumber (OfNat.ofNat 12) (OfNat.ofNat 12))`, and the definitions of ramseyNumber, ForcesRamsey, HasRamseyColoring, IsRamseyFree, SimpleGraph.CliqueFree, IsNClique and IsClique.
- In the control, bit 5 of the literal `badRLit` in Data.lean was flipped in the export (its `natVal` XOR 32), and nothing else was changed. The rejection shows that nanoda actually performs the kernel computations of the proof.
- The exports are not included: 141,524,100 bytes for the complete theorem, and 1.2 MB for each control. Their SHA-256 are in logs_1661/nanoda/exports_not_included.sha256.
- In our run the paths to the two binaries were written into the script. In this copy they are read from LEAN4EXPORT and NANODA instead; nothing else changed.
