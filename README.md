# R(12,12) ≥ 1661

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23963534.svg)](https://doi.org/10.5281/zenodo.23963534)

This repository contains a red/blue colouring of the complete graph K₁₆₆₀ with no monochromatic K₁₂, so R(12,12) ≥ 1661.

To our knowledge this improves our earlier R(12,12) ≥ 1658 ([r1212-1658](https://github.com/YueMa0/r1212-1658), [doi:10.5281/zenodo.23827702](https://doi.org/10.5281/zenodo.23827702)) and the best bound published by others, R(12,12) ≥ 1641 (M. Tatarevic, [arXiv:2608.06531](https://arxiv.org/abs/2608.06531), August 2026). The literature search was last made on 4 November 2026. The result has not been peer reviewed.

## The result

- [graph/r1212_1660.graph](graph/r1212_1660.graph) has 1660 lines of 1660 characters. Character w of line v is 1 if the edge vw is red and 0 if it is blue.
- SHA-256: `07c5cbb696c1d7662870b42e6a1c508e7ef46bf2313f01d297f914e62448867d`.
- It contains no red K₁₂ and no blue K₁₂, so R(12,12) ≥ 1661.
- The result is checked by two independent exhaustive computer searches, and proved in Lean 4 with Mathlib; see [How it was checked](#how-it-was-checked) and [The Lean proof](#the-lean-proof).

## The colouring in brief

- **V°.** Vertices 0–1574 are the Mathon–Shearer (11,11)-colouring M(797), with the 21 vertices of a set Σ_V removed.
- **Σ_V = C ∪ I ∪ {675}.** C, a red K₁₀, and I, a blue K₁₀, are the certificates of r1212-1642 and r1212-1658. 675 = A₆₇₅ is the antipode of the certificate vertex i₆ = 1472 = B₆₇₅.
- **Antipodes.** In M(797), A_x and B_x are antipodal, and so are a and b: towards every other vertex they have opposite colours. So no vertex of V° has the same colour to both vertices of an antipodal pair. Σ_V contains two antipodal pairs: {a, b}, as in r1212-1658, and the new pair {i₆, 675}.
- **The core.** The 85 core vertices 1575–1659 each behave in one of three ways towards V°:
  - **copy** of a vertex g of Σ_V: the core vertex has the colour of g to every vertex of V°;
  - **constant red**;
  - **constant blue**.
- 63 core vertices are copies, 11 are constant red and 11 constant blue. The colours among the 85 core vertices are not given by a formula; they are the ones in the file.
- [graph/README.md](graph/README.md) lists the type of every core vertex. [graph/r1212_1660.json](graph/r1212_1660.json) has the same data in machine-readable form.

**What is new.** A monochromatic clique of the core that contains copies of both vertices of an antipodal pair cannot be extended into V° at all. With this rule, the bound of the clone projection used for r1212-1658, which needs only that M(797) has no monochromatic K₁₁, is enough to rule out a monochromatic K₁₂. Without it, the bound fails for 5,332 cliques of the core. r1212-1658 has 1576 + 81 = 1657 vertices; moving 675 from V° into Σ_V costs nothing, and the core now has 85 vertices, so 1575 + 85 = 1660.

## How it was checked

| Check | What it establishes | Where | Cost |
|---|---|---|---|
| quick check | no monochromatic K₁₂, given that M(797) has no monochromatic K₁₁ and that antipodal vertices have opposite colours to every other vertex (both checked by the script) | verify/check_antipodal_projection.py | seconds |
| exhaustive search | no monochromatic K₁₂ in graph/r1212_1660.graph, without using any structure of the graph | verify/bruteforce_kclique.c; the output of our run is in verify/results/ | 15.5 CPU-hours: 3 h 05 min with 5 threads on an Apple M4 Mac mini |
| independent exhaustive search | the same, with a program written separately that splits the problem differently | verify/independent/ | 17.9 CPU-hours: 2 h 14 min with 8 threads on the same computer |
| output checks | each search output has each of the 3,320 tasks exactly once, with the right task sizes, and every result is "none" | verify/check_bruteforce_output.py, verify/independent/check_indep_output.py | seconds |
| Lean proof | R(12,12) ≥ 1661, from the (11,11) property of M(797) (proved in Lean in r1212-1642), the antipodal property and finite checks that the Lean kernel evaluates | lean/ | see [Checking it yourself](#checking-it-yourself) |

- **The quick check** rebuilds M(797) from its definition, checks that vertices 0–1574 are M(797) minus Σ_V, and reads the type of every core vertex from the file. It then checks every monochromatic clique inside the core, not only the maximal ones: 342,582 red and 236,100 blue. The argument is in its docstring.
- **The exhaustive search** uses the program of r1212-1642 and r1212-1658, unchanged. Every monochromatic K₁₂ has a smallest vertex v, and its other 11 vertices come after v and have colour c to v. So for each vertex v and colour c, the program decides whether those later vertices contain a K₁₁ of colour c. Each pair (v, c) is one task.
- **The independent search** was written for our re-verification of r1212-1658. It shares no code with the first program, and it orders the vertices of each colour by repeatedly removing a vertex of minimum degree, so the two programs solve different subproblems.
- **Controls.** verify/controls/ has the quick check run on three perturbed copies of the colouring and once without the antipodal rule; all four runs fail as they should. Both search programs were tested earlier on 3 November 2026, when we re-verified r1212-1658; [verify/README.md](verify/README.md) describes these tests.

## The Lean proof

[lean/](lean/) proves, in Lean 4.32.1 with Mathlib,

```lean
theorem RamseyIncrement.R1661.r1212_lower_bound : 1661 ≤ ramseyNumber 12 12
```

where `ramseyNumber` is Tatarevic's definition, as in r1212-1642 and r1212-1658: the least n such that every red/blue colouring of K_n has a red K_k or a blue K_s. lean/AxiomAudit1661.lean also restates the result in Mathlib's terms, for a graph on `Fin 1660` and its complement.

- **The colouring.** lean/RamseyIncrement/R1661/Graph.lean defines it on V° ⊕ Fin 85, using tables that lean/gen/gen_data_1661.py generates from graph/r1212_1660.graph (in Data.lean).
- **The argument** is the clone projection with the antipodal rule.
  - A clique with a constant vertex of the other colour, or with copies of both vertices of an antipodal pair, lies inside the core. The kernel checks that the core has no monochromatic K₁₂.
  - For all other cliques the proof reuses the defect lemma and the four small checks of r1212-1658, applied with the edges between copies of antipodal types removed. These cover every such clique, not only the maximal ones.
  - It uses three facts about M(797): it is an (11,11)-colouring (proved in Lean in r1212-1642); antipodal vertices have opposite colours to every other vertex (proved here, from −1 being a square mod 797); and its colours on Σ_V (by kernel computation).
  - It does not use the exhaustive searches.
- **Axioms**: only propext, Classical.choice and Quot.sound. No `sorry`, no `native_decide`.
- **Independent kernels.** leanchecker replayed each of the 25 modules of the proof separately, and nanoda, a Lean kernel written separately in Rust, checked the theorem together with all 29,313 declarations it uses, Mathlib included. Both accepted the proof. nanoda rejected a copy with one bit of a table changed.
- **Not part of the proof**: that the colouring defined in Lean is the published file. lean/tools/compare_export_1661.py rebuilds all 1660 × 1660 = 2,755,600 entries from Data.lean, following the definitions in Graph.lean, and they equal the file; so do the 85 core rows that Lean's interpreter evaluated.

20 of the 25 modules come unchanged from r1212-1642 (19) and r1212-1658 (the defect lemma); 5 of the 19 come from Tatarevic's repository ([UPSTREAM.md](UPSTREAM.md)). The new modules are in lean/RamseyIncrement/R1661/. [lean/audit/README.md](lean/audit/README.md) explains how to build and audit the proof, and records our runs.

## How this work was done

The colouring was found on 3 November 2026 by Yue Ma together with Claude (Claude Opus 5.5, by Anthropic), working as agents in Claude Code. The research continues r1212-1658, which started from exploratory work by GPT-6 Astra (OpenAI); its history is described there. Yue Ma chose the research direction, approved each stage and decides how the result is published. Claude designed and ran the searches, and prepared the checks in verify/. Claude also wrote the Lean proof in lean/, and ran its builds and kernel checks recorded in lean/audit/. All computations, the searches, the exhaustive checks and the Lean builds, were run on an Apple M4 Mac mini.

## Checking it yourself

The quick check needs Python 3 with numpy and networkx, and takes seconds:

```bash
python3 verify/check_antipodal_projection.py graph/r1212_1660.graph
```

It should end with `CHECK: PASS`.

The exhaustive search needs a C compiler. It takes about 15.5 CPU-hours, about 2 hours with 8 threads on an Apple M4. Start with a new output file each time; verify/README.md explains why.

```bash
cc -O3 -pthread -o bruteforce_kclique verify/bruteforce_kclique.c
./bruteforce_kclique graph/r1212_1660.graph 12 bruteforce.jsonl 8
python3 verify/check_bruteforce_output.py graph/r1212_1660.graph bruteforce.jsonl --t 12
```

The last command should print `RESULT: no monochromatic K12` and `CHECK: PASS`. It can also check the output of our run:

```bash
python3 verify/check_bruteforce_output.py graph/r1212_1660.graph verify/results/candidate_1660.jsonl --t 12
```

[verify/independent/README.md](verify/independent/README.md) describes the independent search in the same way.

The Lean proof needs [elan](https://github.com/leanprover/elan), which installs the Lean version in lean/lean-toolchain, and up to about 7 GB of memory. The script first downloads the Mathlib cache and then builds the modules that need much memory one at a time. On an Apple M4 Mac mini a build from scratch took 14.5 minutes, with at most 6.6 GB of memory; lean/audit/README.md has the records.

```bash
bash lean/audit/build_r1661.sh
```

It ends by printing the axioms of the main theorems; lean/audit/logs_1661/axioms.out has our output.

## Layout

| Path | Contents |
|---|---|
| graph/ | the colouring, its SHA-256, its vertex order and the type of every core vertex |
| verify/ | the quick check and its controls, the two exhaustive search programs with their output checkers, and the outputs of our runs |
| lean/ | the Lean proof, the scripts to build and audit it, and the records of our runs |
| UPSTREAM.md | the files in lean/ that come from r1212-1642, r1212-1658 and Tatarevic's repository |

## Credits

- The (11,11)-colouring M(797) is due to Mathon (1987) and Shearer (1986).
- **Milos Tatarevic**: the two-parameter increment R(k+1, s+1) ≥ R(k,s) + 2k + 2s ([arXiv:2608.06531](https://arxiv.org/abs/2608.06531)), and his Lean development, which provides the definition of `ramseyNumber` and the basic lemmas used here.
- From r1212-1642 and r1212-1658: the certificates C and I, the exhaustive search program and its output checker, the clone projection, and 20 Lean modules; see UPSTREAM.md.
- **New in this repository**: the colouring; the antipodal rule and the quick check verify/check_antipodal_projection.py; the independent search program in verify/independent/; and the Lean proof in lean/RamseyIncrement/R1661/ with its tools.
- **Author**: Yue Ma. For the role of AI, see [How this work was done](#how-this-work-was-done).

## How to cite

Each release is archived on Zenodo. To cite all versions, use [doi:10.5281/zenodo.23963534](https://doi.org/10.5281/zenodo.23963534). Version 1.0.0 is [doi:10.5281/zenodo.23963535](https://doi.org/10.5281/zenodo.23963535). Citation metadata is in [CITATION.cff](CITATION.cff); GitHub shows it under "Cite this repository". Please cite Tatarevic's paper, r1212-1642 and r1212-1658 as well.

## License

MIT; see [LICENSE](LICENSE).
