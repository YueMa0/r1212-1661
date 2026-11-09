# Computer checks of the colouring

These programs read graph/r1212_1660.graph.

## Quick check: clone projection with the antipodal rule

check_antipodal_projection.py needs Python 3.9 or later with numpy and networkx, and takes a few seconds.

```bash
python3 verify/check_antipodal_projection.py graph/r1212_1660.graph
```

It uses two facts about M(797):

- M(797) has no monochromatic K₁₁ (Mathon 1987, Shearer 1986; checked by computer and proved in Lean in r1212-1642). The script uses this fact; it does not check it;
- antipodal vertices (A_x and B_x, and a and b) have opposite colours to every other vertex. The script checks this for all 798 pairs.

It rebuilds M(797) from its definition and checks that vertices 0–1574 of the file are M(797) minus Σ_V, in increasing order. It reads the type of each of the 85 core vertices from the file. Then it checks every monochromatic clique inside the core that has no constant vertex of the other colour, not only the maximal ones, against the bound of the clone projection, with the antipodal rule; a clique with such a vertex cannot be extended into V°, and the script checks that the largest monochromatic clique inside the core has 11 vertices. The argument is in its docstring.

- `--no-antipodal` drops the antipodal rule, as a control that must fail.
- An argument `u:v` flips the colour of the edge uv first, as a negative control.

[controls/](controls/) has the outputs of these runs; [controls/README.md](controls/README.md) lists them.

## Checkers A and B

[crosscheck/](crosscheck/) has two more programs for the clone model, written separately from the quick check and from each other. They check the exact criterion: for every monochromatic clique of the core, the largest clique of M(797) that extends it is computed exactly, not bounded. Checker A (Python with numpy, and a small C library) can also use the bound of the quick check, with or without the antipodal rule. Checker B (C) reads the types of the core vertices from a file that a short Python script writes from graph/r1212_1660.json. Each takes a few seconds.

```bash
cc -O3 -shared -fPIC -o libecg.so verify/crosscheck/checker_a/ecg.c
python3 verify/crosscheck/checker_a/exact_check_general.py graph/r1212_1660.graph graph/r1212_1660.json
cc -O3 -o xcheck verify/crosscheck/checker_b/xcheck.c
python3 verify/crosscheck/checker_b/types_from_json.py graph/r1212_1660.json > r1212_1660.types
./xcheck graph/r1212_1660.graph r1212_1660.types
```

Both pass. [crosscheck/README.md](crosscheck/README.md) states the criterion and the options, and lists our runs, including two controls of checker A that fail as they should; the outputs are in [crosscheck/results/](crosscheck/results/).

## Exhaustive search

bruteforce_kclique.c uses no structure of the graph. Every monochromatic K₁₂ has a smallest vertex v, and its other 11 vertices are later vertices joined to v in its colour c. So for each v and c the program decides whether P(v,c) = {w > v : colour(v,w) = c} contains a K₁₁ of colour c. That is 3,320 tasks, each an exact bitset branch and bound. The largest task has |P(v,c)| = 834.

```bash
cc -O3 -pthread -o bruteforce_kclique verify/bruteforce_kclique.c
./bruteforce_kclique graph/r1212_1660.graph 12 bruteforce.jsonl 8
python3 verify/check_bruteforce_output.py graph/r1212_1660.graph bruteforce.jsonl --t 12
```

- The program is the one of r1212-1642 and r1212-1658, unchanged: SHA-256 541a83313b5e78e9246953ea0f597db63db01f8f18fa2b475b795109b1056e44. The last argument is the number of threads.
- On restart, a task counts as finished if a line of the output file merely starts with its (v, c). So **always start with a new output file**, or remove a truncated last line first.
- check_bruteforce_output.py needs only the Python standard library. It checks that every task appears exactly once, that each task size equals |P(v,c)| computed from the graph, and that every result is "none". It prints `CHECK: PASS` or `CHECK: FAIL`.

## Independent exhaustive search

[independent/](independent/) has a second exhaustive search, indep_kclique.c, written separately and sharing no code with bruteforce_kclique.c. It splits the problem differently, so the two programs solve different subproblems. [independent/README.md](independent/README.md) describes it.

## Our runs

Both runs were made on 3 November 2026 on an Apple M4 Mac mini.

| Run | Program | Threads | Result | Nodes | CPU time |
|---|---|---|---|---|---|
| [results/](results/) | bruteforce_kclique | 5 | all 3,320 tasks "none", `CHECK: PASS` | 2.236 × 10¹¹ | 15.46 h |
| [independent/results/](independent/results/) | indep_kclique | 8 | all 3,320 tasks "none", `CHECK: PASS` | 2.403 × 10¹¹ | 17.93 h |

The same two binaries were tested earlier on 3 November 2026, when we re-verified r1212-1658:

- bruteforce_kclique reproduced the published run of r1212-1658 task by task, including node counts, and found the K₁₂s planted in its two control colourings;
- indep_kclique agreed with an exact oracle on 528 random graphs (116,688 task results), caught 4 deliberately broken versions of itself, and found all 14 planted K₁₂s it was given.

The records of those tests are not part of this repository.
