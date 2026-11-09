"""Checker A: exact check that a colouring of clone type over M(797) has no monochromatic K12,
for any target set Sigma_V of at most 32 vertices of M(797).

usage: exact_check_general.py GRAPH META.json [--bound | --bound-anti] [--flip u:v ...] [--lib LIB]

GRAPH: n lines of n characters; character w of line v is 1 iff the edge vw is red.
META.json: the description of the colouring in the format of graph/r1212_1660.json: Sigma_V; file
vertices 0..|V0|-1 are V0 = M(797) minus Sigma_V, in increasing order; every other file vertex has a
declared type: copy of a vertex g of Sigma_V, constant red or constant blue.
LIB: the e_c oracle ecg.c built as a shared library (default ./libecg.so).

Criterion.  Let T be the file vertices outside V0 and tau(f) the type of f in T.  For a colour c and
D in Sigma_V let N0_c(D) = {v in V0 : gv has colour c in M(797) for all g in D} and let e_c(D) be the
size of the largest c-clique of M(797) inside N0_c(D).  A c-clique Q of the file splits into
K = Q n T and K0 = Q n V0.  If K contains a constant vertex of the other colour, K0 is empty;
otherwise K0 can be any c-clique of M(797) inside N0_c(D(K)), where D(K) = {tau(f) : f in K a copy}.
So the file has no monochromatic K12 iff for each colour c and each c-clique K of T:
  (i) |K| <= 11 if K contains a constant vertex of the other colour;
  (ii) |K| + e_c(D(K)) <= 11 otherwise.
(ii) need not be monotone in K, so every clique is checked, not only the maximal ones.

The script
  1. rebuilds M(797) from its definition and checks every V0-V0 edge of the file against it;
  2. checks every T-V0 edge against the declared type (copy of g / constant red / constant blue),
     and also re-derives the type from the file;
  3. for each colour c: checks that the largest c-clique inside T has <= 11 vertices, and that
     every c-clique K of T without a constant point of the other colour (all of them, not only
     maximal ones) satisfies |K| + e_c(D(K)) <= 11, with e_c computed fresh by the C oracle.
Together these are equivalent to "no monochromatic K12".  The values e_c are exact given that
M(797) has no monochromatic K11 (Mathon 1987); see ecg.c.
With --bound, e_c is replaced by the sufficient bound 10 - omega^M_c(D) (the clone projection of
r1212-1658).
With --bound-anti, the same bound, except e_c(D) = 0 when D contains an antipodal pair
(A_x, B_x or a, b: every other vertex of M(797) has opposite colours to the two; asserted below);
violations are then listed by D with the exact e_c(D) that would be needed instead.
--flip u:v flips the colour of the edge uv of the file first (negative controls).
In the exact mode, violations are turned into explicit K12 witnesses in the file and re-checked
edge by edge."""
import ctypes, hashlib, json, sys
from collections import Counter
from pathlib import Path
import numpy as np

args = sys.argv[1:]
use_bound = "--bound" in args
use_anti = "--bound-anti" in args
flips = [a for i, a in enumerate(args) if i > 0 and args[i - 1] == "--flip"]
libpath = ([a for i, a in enumerate(args) if i > 0 and args[i - 1] == "--lib"] or ["libecg.so"])[-1]
gpath, mpath = args[0], args[1]
raw = open(gpath, "rb").read()
sha = hashlib.sha256(raw).hexdigest()
print("graph", gpath, "sha256", sha)
rows = raw.split(b"\n")
assert rows[-1] == b"", "file must end with LF"
n = len(rows) - 1
G = np.array([np.frombuffer(r, dtype=np.uint8) - 48 for r in rows[:-1]], dtype=np.uint8)
assert G.shape == (n, n) and set(np.unique(G).tolist()) <= {0, 1}
assert (G == G.T).all() and not np.diag(G).any()
for f in flips:
    u, v = map(int, f.split(":"))
    G[u, v] = G[v, u] = 1 - G[u, v]
    print(f"PERTURBED: flipped {u}-{v} to {'red' if G[u, v] else 'blue'}")
meta = json.load(open(mpath))
SIG = [int(x) for x in meta["Sigma_V"]["vertices"]]
SIGNAME = meta["Sigma_V"]["names"]
assert len(SIG) <= 32 and len(set(SIG)) == len(SIG) and len(SIGNAME) == len(SIG)
SNAME = [str(g) for g in SIG]
lib = ctypes.CDLL(str(Path(libpath).resolve()))
lib.ec_init(len(SIG), (ctypes.c_int * len(SIG))(*SIG))
for _nm in ("ec_get", "ec_bound"):
    getattr(lib, _nm).argtypes = [ctypes.c_int, ctypes.c_uint32]
lib.ec_compute_ub.argtypes = [ctypes.c_int, ctypes.c_uint32, ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_longlong)]
# declared role of every file vertex: {"M": m} (vertex m of V0) or {"T": type}, type = str(g) for g in Sigma_V, "R" or "B"
assert int(meta["n"]) == n, (meta["n"], n)
n0 = int(meta["V0"]["size"])
assert meta["V0"]["file_vertices"] == [0, n0 - 1]
V0decl = [v for v in range(1596) if v not in set(SIG)]
roles = [{"M": m} for m in V0decl[:n0]] + [None] * (n - n0)   # file vertex v < |V0|: the v-th vertex of M(797) outside Sigma_V
for e in meta["core_vertices"]:
    v = int(e["vertex"])
    assert n0 <= v < n and roles[v] is None, v
    if e["type"] == "copy":
        g = int(e["of_vertex"])
        assert SIGNAME[SIG.index(g)] == e["of"], e
        roles[v] = {"T": str(g)}
    else:
        roles[v] = {"T": {"constant red": "R", "constant blue": "B"}[e["type"]]}
assert None not in roles, "every file vertex outside V0 needs a declared type"
print("Sigma_V:", SIG)
assert len(roles) == n, (len(roles), n)

# M(797) from the definition
p = 797
sq = np.zeros(p, dtype=bool); sq[(np.arange(1, p) ** 2) % p] = True
x = np.arange(p); d = (x[:, None] - x[None, :]) % p
M = np.zeros((1596, 1596), dtype=np.uint8)
M[:p, :p] = M[p:2*p, p:2*p] = sq[d] & (d != 0)
M[:p, p:2*p] = (~sq[d]) & (d != 0); M[p:2*p, :p] = M[:p, p:2*p].T
M[1594, :p] = M[:p, 1594] = 1; M[1595, p:2*p] = M[p:2*p, 1595] = 1
V0all = [v for v in range(1596) if v not in set(SIG)]
NS = len(SIG)
def antipode(g): return {1594: 1595, 1595: 1594}.get(g, g + 797 if g < 797 else g - 797)
PAIRS = [(1 << i) | (1 << j) for i in range(NS) for j in range(i + 1, NS) if antipode(SIG[i]) == SIG[j]]
for g in range(1596): assert antipode(antipode(g)) == g and (M[g] + M[antipode(g)] == 1)[[w for w in range(1596) if w not in (g, antipode(g))]].all()
print("antipodal pairs inside Sigma_V:", [[SIG[i] for i in range(NS) if P >> i & 1] for P in PAIRS])

Vpos = [i for i, r in enumerate(roles) if "M" in r]
Vm = [roles[i]["M"] for i in Vpos]
assert len(set(Vm)) == len(Vm) and set(Vm) <= set(V0all)
assert sorted(Vm) == V0all, "V0 must be all M points outside Sigma_V"
assert (G[np.ix_(Vpos, Vpos)] == M[np.ix_(Vm, Vm)]).all(), "V0 block differs from M(797)"
print(f"V0: {len(Vpos)} vertices, all V0-V0 edges equal M(797)")
TNAMES = SNAME + ["R", "B"]
RI, BI = NS, NS + 1
Tpos = [i for i, r in enumerate(roles) if "T" in r]
types = []
for i in Tpos:
    t = TNAMES.index(roles[i]["T"])
    row = G[i, Vpos]
    want = M[SIG[t], Vm] if t < NS else np.full(len(Vm), 1 if t == RI else 0, dtype=np.uint8)
    assert (row == want).all(), f"vertex {i}: edges to V0 are not of declared type {TNAMES[t]}"
    derived = [TNAMES[s] for s in range(NS) if (M[SIG[s], Vm] == row).all()]
    derived += ["R"] if row.all() else []
    derived += ["B"] if not row.any() else []
    assert derived == [TNAMES[t]], (i, derived)
    types.append(t)
nT = len(Tpos)
print(f"T: {nT} vertices; total {n} = {len(Vpos)} + {nT}; type counts",
      dict(sorted(Counter(TNAMES[t] for t in types).items(), key=lambda kv: TNAMES.index(kv[0]))))
CT = G[np.ix_(Tpos, Tpos)]

ecache = {}
def cap(c, D):
    k = (c, D)
    if k not in ecache:
        if use_anti and any(D & P == P for P in PAIRS): ecache[k] = 0
        else: ecache[k] = lib.ec_bound(c, D) if (use_bound or use_anti) else lib.ec_get(c, D)
    return ecache[k]

def witness(c, D, size):
    buf = (ctypes.c_int * 64)(); nodes = ctypes.c_longlong()
    r = lib.ec_compute_ub(c, D, size, buf, ctypes.byref(nodes))
    assert r >= size
    return list(buf[:size])

bad_total = 0
for c, cname in ((1, "red"), (0, "blue")):
    adj = [sum(1 << j for j in range(nT) if j != i and CT[i, j] == c) for i in range(nT)]
    # (a) largest c-clique in T
    best = 0
    def mc(P, sz):
        global best
        if sz > best: best = sz
        while P:
            if sz + bin(P).count("1") <= best: return
            v = P.bit_length() - 1; P &= ~(1 << v)
            mc(P & adj[v], sz + 1)
    mc((1 << nT) - 1, 0)
    print(f"[{cname}] largest {cname} clique inside T: {best} ({'ok' if best <= 11 else 'FAIL'})")
    bad_total += best > 11
    # (b) all c-cliques without a constant point of the other colour
    other = BI if c == 1 else RI
    allowed = sum(1 << i for i in range(nT) if types[i] != other)
    tbit = [(1 << types[i]) if types[i] < NS else 0 for i in range(nT)]
    hist, sizes, bad = Counter(), Counter(), []
    stack = [(0, 0, allowed, 0)]          # (|K|, D, candidates, K bitmask)
    count = 0
    while stack:
        sz, D, P, K = stack.pop()
        if sz:
            count += 1
            sizes[sz] += 1
            s = 11 - sz - cap(c, D)
            hist[s] += 1
            if s < 0: bad.append((K, D))
        while P:
            v = P.bit_length() - 1; P &= ~(1 << v)
            stack.append((sz + 1, D | tbit[v], P & adj[v], K | (1 << v)))
    print(f"[{cname}] cliques checked (all, not only maximal): {count}; by size {dict(sorted(sizes.items()))}")
    print(f"[{cname}] slack 11-|K|-cap histogram: {dict(sorted(hist.items()))}")
    print(f"[{cname}] violations: {len(bad)}")
    bad_total += len(bad)
    if use_anti and bad:
        byD = {}
        for K, D in bad:
            byD.setdefault(D, []).append(bin(K).count("1"))
        print(f"[{cname}] distinct D among violations: {len(byD)}")
        rowsD = []
        for D, ks in byD.items():
            ex = lib.ec_get(c, D)
            rowsD.append((-len(ks), D, max(ks), cap(c, D), ex))
        for nk, D, kmax, bd, ex in sorted(rowsD)[:20]:
            print(f"    D = {[SIG[j] for j in range(NS) if D >> j & 1]}: bound {bd}, exact {ex}, bound-exact {bd - ex}, "
                  f"violating cliques {-nk}, max |K| {kmax}, exact ok: {kmax + ex <= 11}")
        allD = sorted(rowsD)
        print(f"[{cname}] all {len(allD)} D: exact ok for every violating clique: "
              f"{all(kmax + ex <= 11 for _, _, kmax, _, ex in allD)}; bound-exact histogram "
              f"{dict(sorted(Counter(bd - ex for _, _, _, bd, ex in allD).items()))}")
    for K, D in sorted(bad, key=lambda kd: bin(kd[0]).count("1"))[:5]:
        Kl = [i for i in range(nT) if K >> i & 1]
        names = [TNAMES[types[i]] for i in Kl]
        e = cap(c, D)
        print(f"    K = file vertices {[Tpos[i] for i in Kl]} types {names}, cap {e}")
        if not (use_bound or use_anti):
            need = max(0, 12 - len(Kl))
            W = [Vpos[Vm.index(m)] for m in witness(c, D, need)] if need else []
            Q = [Tpos[i] for i in Kl][:12] + W
            ok = len(Q) == 12 and all(G[a, b] == c for a in Q for b in Q if a != b)
            print(f"      explicit {cname} K12 in the file: {sorted(Q)} -> {'confirmed' if ok else 'NOT confirmed'}")
print("model:", "bound 10 - omega^M_c(D), 0 on antipodal pairs" if use_anti else
      ("bound 10 - omega^M_c(D)" if use_bound else "exact e_c(D)"))
print("CHECK:", "PASS" if bad_total == 0 else f"FAIL ({bad_total})")
sys.exit(0 if bad_total == 0 else 1)
