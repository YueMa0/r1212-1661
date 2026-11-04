"""Exact check that the 1660-vertex file graph/r1212_1660.graph has no monochromatic K12, using only
(1) that M(797) has no monochromatic K11 (Mathon 1987; checked by computer in r1212-1642), and
(2) that antipodal vertices of M(797) have complementary colours to all other vertices (asserted below).

Uses nothing from the search that found the colouring and no exact clique sizes inside M(797);
only the file and the target set Sigma_V (the certificates C u I of r1212-1642, plus 675).

Layout: V0 = M(797) minus Sigma_V (1575 vertices). Vertices 0..1574 of the file are V0 in
increasing order (checked: this block must equal M(797) rebuilt from its definition); the other
vertices form T.

Method (clone projection with the antipodal rule):
- Each t in T must be, on V0, constant red, constant blue, or an exact copy of a unique g in Sigma_V.
  The types are read from the file.
- Antipodes in M(797): A_x <-> B_x and a <-> b. Each pair is blue, and for every other vertex w the two
  edges to w have different colours.
- A colour-c clique Q of the whole graph splits as K = Q n T and K0 = Q n V0.
  (i) If K has a member that is constant not-c, K0 is empty, so |Q| <= omega_c(T).
  (ii) Otherwise K0 is a c-clique of M(797) inside N_c(g) for every g in D(K) = {targets of copies in K}.
       Bound: for any c-clique D' of M(797) inside D(K), K0 u D' is a c-clique of M(797), so
       |K0| <= 10 - omega^M_c(D(K)).
       Antipodal rule: if D(K) contains an antipodal pair, no vertex of V0 is c to both, so K0 is empty.
  So Q has at most 11 vertices if omega_c(T) <= 11 and |K| <= cap(D(K)) for every clique K of (ii),
  where cap(D) = 11 if D contains an antipodal pair and 1 + omega^M_c(D) otherwise.
- Under the antipodal rule cap can jump when K grows, so every clique is checked, not only the
  maximal ones.

Options: --no-antipodal drops the antipodal rule (pure bound model; a control that should fail).
u:v flips the colour of edge uv before checking (negative controls).
"""
import hashlib
from pathlib import Path
import sys

import networkx as nx
import numpy as np

args = sys.argv[1:]
antipodal = "--no-antipodal" not in args
args = [a for a in args if a != "--no-antipodal"]
path = args[0]
raw = Path(path).read_bytes()
print("sha256", hashlib.sha256(raw).hexdigest())
lines = raw.split(b"\n")
n = len(lines) - 1
if (n < 1 or lines[-1] != b""
        or any(len(row) != n or set(row) - {48, 49} for row in lines[:-1])):
    raise SystemExit("CHECK FAILED: expected n binary LF-terminated rows of length n")
O = np.array([np.frombuffer(l, dtype=np.uint8) - 48 for l in lines[:-1]], dtype=np.uint8)
if not (O == O.T).all() or np.diag(O).any():
    raise SystemExit("CHECK FAILED: expected a symmetric graph with zero diagonal")
for spec in args[1:]:  # perturbations for negative controls: u:v flips the colour of edge uv
    u_, v_ = map(int, spec.split(":"))
    if not (0 <= u_ < n and 0 <= v_ < n and u_ != v_):
        raise SystemExit("CHECK FAILED: perturbation must name two distinct vertices in range")
    O[u_, v_] = O[v_, u_] = 1 - O[u_, v_]
    print(f"PERTURBED: flipped edge {u_}-{v_} to {'red' if O[u_, v_] else 'blue'}")

# --- M(797) from its definition: A_x = x, B_x = 797 + x, a = 1594, b = 1595
q, nV = 797, 1596
sq = np.zeros(q, dtype=bool)
sq[(np.arange(1, q) ** 2) % q] = True
d = (np.arange(q)[:, None] - np.arange(q)[None, :]) % q
M = np.zeros((nV, nV), dtype=np.uint8)
M[:q, :q] = M[q:2 * q, q:2 * q] = sq[d]
M[:q, q:2 * q] = ~sq[d] & (d != 0)
M[q:2 * q, :q] = M[:q, q:2 * q].T
M[2 * q, :q] = M[:q, 2 * q] = 1
M[2 * q + 1, q:2 * q] = M[q:2 * q, 2 * q + 1] = 1
assert (M == M.T).all() and not np.diag(M).any()

ant = np.concatenate([np.arange(q, 2 * q), np.arange(q), [2 * q + 1, 2 * q]])
comp = (M + M[ant]) == 1  # comp[v, w]: v and its antipode differ towards w
comp[np.arange(nV), np.arange(nV)] = comp[np.arange(nV), ant] = True
if not comp.all() or M[np.arange(nV), ant].any():
    raise SystemExit("CHECK FAILED: antipodal complementarity does not hold in M(797)")
print(f"antipodes: all {nV // 2} pairs are blue and complementary towards the other {nV - 2} vertices")

C = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595]
I = [1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267]
Sigma = C + I + [675]
role = {v: f"c{p}" for p, v in enumerate(C)} | {v: f"i{t}" for t, v in enumerate(I)} | {675: "i6bar"}
V0 = np.array([v for v in range(nV) if v not in set(Sigma)])
n0 = len(V0)
T = list(range(n0, n))
if not (O[:n0, :n0] == M[np.ix_(V0, V0)]).all():
    raise SystemExit("CHECK FAILED: vertices 0..%d are not V0 of M(797) in increasing order" % (n0 - 1))
print(f"V0: {n0} vertices, equal to M(797) minus Sigma_V; T: {len(T)} vertices; total {n}")

# --- types of the T vertices on V0, read from the file
types = {}
for t in T:
    row = O[t, :n0]
    if row.all():
        types[t] = "R"
    elif not row.any():
        types[t] = "B"
    else:
        hits = [g for g in Sigma if (M[g, V0] == row).all()]
        if len(hits) != 1:
            raise SystemExit(f"CHECK FAILED: vertex {t} is not constant or a copy of a unique g in Sigma_V")
        types[t] = hits[0]
counts = {}
for t in T:
    k = types[t] if types[t] in ("R", "B") else role[types[t]]
    counts[k] = counts.get(k, 0) + 1
print("types:", " ".join(f"{k}:{counts[k]}" for k in sorted(counts, key=lambda k: (len(k) > 1, k))))

idx = {g: i for i, g in enumerate(Sigma)}
pairs = [(g, int(ant[g])) for g in Sigma if int(ant[g]) in idx and g < ant[g]]
print("antipodal pairs in Sigma_V:", [(role[g], role[h]) for g, h in pairs],
      "(rule ON)" if antipodal else "(rule OFF: pure bound model)")
bit = {t: (0 if types[t] in ("R", "B") else 1 << idx[types[t]]) for t in T}

# --- omega^M_c(D) for every D in Sigma_V, by recursion on the highest vertex of D
m = len(Sigma)
masks = np.arange(1 << m)
rng = np.random.default_rng(0)
total_bad = 0
for c, cname, other in [(1, "red", "B"), (0, "blue", "R")]:
    w = np.zeros(1 << m, dtype=np.int8)
    for i in range(m):
        low = sum(1 << j for j in range(i) if M[Sigma[i], Sigma[j]] == c)
        L = np.arange(1 << i)
        w[(1 << i) + L] = np.maximum(w[L], 1 + w[L & low])
    for D in [(1 << m) - 1] + list(rng.integers(0, 1 << m, 200)):  # spot check against networkx
        vs = [Sigma[i] for i in range(m) if D >> i & 1]
        g = nx.Graph()
        g.add_nodes_from(vs)
        g.add_edges_from((u, x) for j, u in enumerate(vs) for x in vs[j + 1:] if M[u, x] == c)
        assert w[D] == max((len(k) for k in nx.find_cliques(g)), default=0)
    cap = (1 + w).astype(np.int8)
    if antipodal:
        for g, h in pairs:
            pm = (1 << idx[g]) | (1 << idx[h])
            cap[(masks & pm) == pm] = 11

    g = nx.Graph()
    g.add_nodes_from(T)
    g.add_edges_from((u, x) for j, u in enumerate(T) for x in T[j + 1:] if O[u, x] == c)
    w_T = max(len(k) for k in nx.find_cliques(g))
    print(f"[{cname}] largest {cname} clique inside T: {w_T} ({'ok' if w_T <= 11 else 'FAIL'})")
    total_bad += w_T > 11
    g.remove_nodes_from([t for t in T if types[t] == other])
    count, hist, bad = 0, {}, []
    for K in nx.enumerate_all_cliques(g):
        count += 1
        D = 0
        for t in K:
            D |= bit[t]
        slack = int(cap[D]) - len(K)
        hist[slack] = hist.get(slack, 0) + 1
        if slack < 0:
            bad.append(K)
    print(f"[{cname}] cliques checked (all, not only maximal): {count}; slack histogram {dict(sorted(hist.items()))}")
    print(f"[{cname}] violations (|K| > cap(D(K))): {len(bad)}")
    for K in bad[:5]:
        print("    ", sorted(K), "D =", sorted({role[types[t]] for t in K if bit[t]}))
    total_bad += len(bad)
print("model:", "cap 1 + omega^M_c(D), 11 if D contains an antipodal pair" if antipodal
      else "cap 1 + omega^M_c(D) (no antipodal rule)")
print("RESULT:", "no monochromatic K12 (given M(797) has no monochromatic K11)" if total_bad == 0
      else f"{total_bad} unresolved")
print("CHECK:", "PASS" if total_bad == 0 else "FAIL")
sys.exit(0 if total_bad == 0 else 1)
