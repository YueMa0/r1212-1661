# Output of our run of bruteforce_kclique

The exhaustive search of graph/r1212_1660.graph, run on 3 November 2026 on an Apple M4 Mac mini with 5 threads, 13:16–16:22 EST. [SHA256SUMS](SHA256SUMS) lists the SHA-256 of the files; check with `sha256sum -c SHA256SUMS` in this folder.

| File | Contents |
|---|---|
| candidate_1660.jsonl | one line per task: all 3,320 tasks "none", 223,633,943,462 nodes |
| candidate_1660.meta.txt | start and end time, SHA-256 of the graph, of the source and of the binary, the command |
| candidate_1660.stderr.txt | the program's log |
| candidate_1660.check.txt | the output of check_bruteforce_output.py: `CHECK: PASS`, 15.46 CPU-hours, longest task (10, red) with \|P\| = 834, 170 s |

- The run read the colouring under the name b1660_PM2.graph. It is the same file as graph/r1212_1660.graph, with the same SHA-256 (in candidate_1660.meta.txt and candidate_1660.check.txt).
- In candidate_1660.meta.txt we replaced the host name by "Apple M4 Mac mini" and removed the local directory from the command line. Nothing else changed, but the SHA-256 of that file differs from the one the run wrote; SHA256SUMS lists the file as published here.
- The binary (SHA-256 11dcbe6d…, Apple clang 21.0.0) was rebuilt from the same source on 3 November 2026. It has the same machine code as the binary of the published run of r1212-1658 (37720b55…); the two differ only in the LC_UUID and the code signature.

To check the output against the colouring:

```bash
python3 verify/check_bruteforce_output.py graph/r1212_1660.graph verify/results/candidate_1660.jsonl --t 12
```
