# Outputs of the quick check and its controls

Each file is the output of `python3 verify/check_antipodal_projection.py graph/r1212_1660.graph` with the arguments listed, run on 4 November 2026 with the script in verify/.

| File | Arguments | Expected | Result |
|---|---|---|---|
| pass.txt | none | PASS | `CHECK: PASS`, exit 0. Cliques inside the core checked: 342,582 red and 236,100 blue, all of them; no violation; the largest monochromatic clique inside the core has 11 vertices |
| flip_1615_1616.txt | `1615:1616` | FAIL | `CHECK: FAIL`, exit 1: 2 red violations. 1615 and 1616 are constant red; with the edge red, a constant-red clique can be extended by a red K₁₀ of M(797) |
| no_antipodal.txt | `--no-antipodal` | FAIL | `CHECK: FAIL`, exit 1: 5,332 violations (5,123 red, 209 blue). Without the antipodal rule the bound alone does not suffice |
| flip_0_1600.txt | `0:1600` | rejected | exit 1: vertex 1600 is no longer constant or a copy of a vertex of Σ_V |
| flip_0_1.txt | `0:1` | rejected | exit 1: vertices 0–1574 are no longer M(797) minus Σ_V |

pair_stats.py is the same check with two counters added; it is not part of the check. pair_stats.txt is its output on the colouring. Of the cliques checked, 7,125 red and 10,112 blue have a type set containing an antipodal pair: 87 red and 2,137 blue only {a, b}, 7,038 red and 7,961 blue only {i6, i6bar}, and 14 blue both pairs.
