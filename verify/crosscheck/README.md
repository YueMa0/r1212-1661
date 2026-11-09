# Checkers A and B

Two more programs that check the colouring against the clone model. Unlike the quick check, verify/check_antipodal_projection.py, they can also use the exact criterion below. We wrote them on 3 November 2026, during the search that found the colouring, to check candidates in seconds rather than hours. They were written separately from each other and from the quick check.

In the paper they are the rows "checker A, bound mode" and "checkers A and B, exact mode" of Table 3. Checker A also gives the two controls of Appendix A: flipping the edge 1615–1616, and dropping the antipodal rule.

## The criterion

The file has V° = M(797) minus Σ_V as vertices 0–1574 and the core T as vertices 1575–1659 (see [graph/README.md](../../graph/README.md)). Each core vertex f has a type τ(f): a copy of a vertex g of Σ_V, constant red, or constant blue. For a colour c and D ⊆ Σ_V, let

- N⁰_c(D) be the set of vertices v of V° such that gv has colour c in M(797) for every g in D (N⁰_c(∅) = V°);
- e_c(D) be the size of the largest c-clique of M(797) inside N⁰_c(D).

A c-clique Q of the file splits into K = Q ∩ T and K° = Q ∩ V°. If K contains a constant vertex of the other colour, K° is empty. Otherwise K° can be any c-clique of M(797) inside N⁰_c(D(K)), where D(K) is the set of the types of the copies in K. So the file has no monochromatic K₁₂ if and only if, for each colour c and every c-clique K of T:

1. |K| ≤ 11, if K contains a constant vertex of the other colour;
2. |K| + e_c(D(K)) ≤ 11, otherwise.

Condition 2 need not be monotone in K, so both checkers check every clique of T, not only the maximal ones.

If D contains an antipodal pair, N⁰_c(D) is empty and e_c(D) = 0. The quick check replaces e_c(D) by the bound 10 − ω_c(D), where ω_c(D) is the largest c-clique of M(797) inside D. It also uses e_c(D) = 0 when D contains an antipodal pair. The bound holds because M(797) has no monochromatic K₁₁. Both checkers compute e_c(D) by an exhaustive branch and bound that stops once it reaches this bound. So their exact values also rely on M(797) having no monochromatic K₁₁.

## Checker A

[checker_a/exact_check_general.py](checker_a/exact_check_general.py) needs Python 3 with numpy. It computes e_c with the C library [checker_a/ecg.c](checker_a/ecg.c), loaded through ctypes. Run from the repository root:

```bash
cc -O3 -shared -fPIC -o libecg.so verify/crosscheck/checker_a/ecg.c
python3 verify/crosscheck/checker_a/exact_check_general.py graph/r1212_1660.graph graph/r1212_1660.json
```

- It rebuilds M(797) from its definition and checks every edge inside V° against it.
- It reads the declared type of every core vertex from graph/r1212_1660.json and checks every edge between T and V° against it. It also derives the type of each core vertex from the file and checks that it is unique and equals the declared one.
- It enumerates the cliques of T of each colour with its own bitset recursion, and checks conditions 1 and 2.
- Without options it uses the exact e_c. A violation is extended by a clique of M(797) to an explicit K₁₂, and the script checks that K₁₂ in the file, edge by edge.
- `--bound-anti` uses the bound with the antipodal rule. This is the criterion of the quick check, computed by different code. For each violation it also prints the exact value e_c(D) that would be needed.
- `--bound` uses the bound without the antipodal rule (the clone projection of r1212-1658). This is a control that must fail.
- `--flip u:v` flips the colour of the edge uv first. `--lib PATH` loads the library from PATH instead of ./libecg.so.

## Checker B

[checker_b/xcheck.c](checker_b/xcheck.c) and the header [checker_b/mlib.h](checker_b/mlib.h) need only a C compiler. The program reads the types from a text file. [checker_b/types_from_json.py](checker_b/types_from_json.py) writes that file from graph/r1212_1660.json, using only the Python standard library.

```bash
cc -O3 -o xcheck verify/crosscheck/checker_b/xcheck.c
python3 verify/crosscheck/checker_b/types_from_json.py graph/r1212_1660.json > r1212_1660.types
./xcheck graph/r1212_1660.graph r1212_1660.types
```

- It rebuilds M(797) from its definition and checks that the V° part of the types file lists every vertex of M(797) outside Σ_V exactly once.
- It checks every edge inside V° against M(797), and every edge between T and V° against the declared types.
- It enumerates all monochromatic cliques of T, including those with a constant vertex of the other colour, and groups the others by their type set D.
- For each colour and each D it takes the largest clique K with D(K) = D. It computes e_c(D) exactly unless the bound already leaves slack, and checks condition 2. It checks condition 1 separately.
- It ends with `PASS` or `FAIL`.

The two checkers count differently. Checker A and the quick check count the cliques without a constant vertex of the other colour: 342,582 red and 236,100 blue. Checker B counts all cliques of T: 1,308,227 red and 1,042,026 blue. Of the cliques without such a constant, B finds 22,840 red and 15,452 blue type sets.

## Our runs

We ran both checkers on 9 November 2026 on an Apple M4 Mac mini, from the repository root, with the commands above. [results/runs.txt](results/runs.txt) has the date, the machine, the compiler, the SHA-256 of the graph and of the sources, and the command, exit code and time of each run. [results/SHA256SUMS](results/SHA256SUMS) lists the SHA-256 of the files in results/.

| Paper | Run | Expected | Result | Output |
|---|---|---|---|---|
| Table 3, checker A, bound mode | A, `--bound-anti` | PASS | `CHECK: PASS`. 342,582 red and 236,100 blue cliques; slack histograms equal to those of verify/controls/pass.txt | [a_bound_anti.txt](results/a_bound_anti.txt) |
| Table 3, checkers A and B, exact mode | A, exact | PASS | `CHECK: PASS`, with the same clique counts | [a_exact.txt](results/a_exact.txt) |
| | B | PASS | `PASS`: no mismatch with M(797) or the types, no violation | [b_exact.txt](results/b_exact.txt) |
| Appendix A, flipping 1615–1616 | A, exact, `--flip 1615:1616` | FAIL | `CHECK: FAIL (2)`. Two red violations: K = {1615, 1616} with D = ∅, and K = {1615, 1616, 1646} with D = {i6}. Each is extended to an explicit red K₁₂, which the script confirms in the flipped file | [a_exact_flip_1615_1616.txt](results/a_exact_flip_1615_1616.txt) |
| | A, `--bound-anti --flip 1615:1616` | FAIL | `CHECK: FAIL (2)`. The same two violations; for both, the bound equals the exact value | [a_bound_anti_flip_1615_1616.txt](results/a_bound_anti_flip_1615_1616.txt) |
| Appendix A, no antipodal rule | A, `--bound` | FAIL | `CHECK: FAIL (5332)`: 5,123 red and 209 blue violations | [a_bound_plain.txt](results/a_bound_plain.txt) |

1615 and 1616 are constant red. With the edge between them red, the clique {1615, 1616} extends by a red K₁₀ of M(797), and {1615, 1616, 1646} by a red K₉ inside the red neighbourhood of i6.

Each run took under 2 seconds.

## Changes since 3 November

The files here are the programs we ran on 3 November 2026, with these changes:

- The comments were rewritten to be self-contained. Checker A's docstring now states the criterion itself.
- Checker A reads graph/r1212_1660.json. On 3 November it read the same declarations in another format. It loads the library from `--lib` or ./libecg.so; before, it loaded a file next to the script. The checking code is unchanged.
- ecg.c: two unused `#include <pthread.h>` lines were removed.
- mlib.h: `#include <alloca.h>` was added, since the code calls alloca.
- types_from_json.py is new. On graph/r1212_1660.json it writes, byte for byte, the types file that checker B read on 3 November.

The counts, histograms, violations and K₁₂ witnesses in results/ are the same as in our outputs of 3 November 2026. Those outputs are not in this repository.
