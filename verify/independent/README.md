# An independent exhaustive search

indep_kclique.c was written for our re-verification of r1212-1658 on 3 November 2026, without reusing code from verify/bruteforce_kclique.c. Its header explains the method:

- **Decomposition.** For each colour c, the vertices are ranked by repeatedly removing a vertex of minimum degree in the colour-c graph (ties: smallest index). Every monochromatic K₁₂ of colour c has a unique vertex v of smallest rank, and its other 11 vertices lie in L(v,c) = {w : colour(v,w) = c, rank_c(w) > rank_c(v)}. So the graph has no monochromatic K₁₂ iff no task (v,c) finds a K₁₁ of colour c in L(v,c). bruteforce_kclique.c uses the file order instead, so the two programs solve different subproblems.
- **Search.** To decide whether a set P contains a k-clique, P is coloured greedily with k − 1 classes; every k-clique meets the uncoloured vertices, and the search branches on them.
- Every reported clique is re-checked against the input. The output file is opened so that the program refuses to overwrite or append.

```bash
cc -O3 -pthread -o indep_kclique verify/independent/indep_kclique.c
./indep_kclique graph/r1212_1660.graph 12 indep.jsonl 8
python3 verify/independent/check_indep_output.py graph/r1212_1660.graph indep.jsonl
```

check_indep_output.py needs numpy. It recomputes the ranks and every task size |L(v,c)| from the graph, checks that every task appears exactly once, and that every result is "none".

## Our run

[results/](results/) has the output of our run, on 3 November 2026 on an Apple M4 Mac mini with 8 threads, 17:18–19:33 EST. All 3,320 tasks are "none": 240,300,925,833 nodes, 17.93 CPU-hours. The largest task has |L(v,c)| = 813; the slowest took 140 s. check_indep_output.py printed `CHECK: PASS` (indep_1660.check.txt). [results/SHA256SUMS](results/SHA256SUMS) lists the SHA-256 of the files.

- The run read the colouring under the name b1660_PM2.graph; it is the same file, with the same SHA-256.
- In indep_1660.meta.txt we replaced the host name by "Apple M4 Mac mini" and removed the local directory from the command line; nothing else changed.
- The program was tested before this run: it agreed with an exact oracle on 528 random graphs (116,688 task results), caught 4 deliberately broken versions of itself, and found all 14 K₁₂s planted into copies of the colouring of r1212-1658. The records of those tests are not part of this repository.
