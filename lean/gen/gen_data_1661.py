"""Generate RamseyIncrement/R1661/Data.lean from the 1660-vertex colouring b1660_PM2.

    python -B gen/gen_data_1661.py GRAPH [--out PATH] [--flip u:v ...] [--allow-other-sha]
                                   [--summary PATH] [--skip-search]

Reads the colouring (n lines of n characters, 1 = red).  File vertices 0-1574 are V°, the
points of M(797) outside Sigma_V in increasing order (M(797) numbering of r1212-1642:
A_x = x, B_x = 797 + x, a = 1594, b = 1595); file vertices 1575-1659 are the 85 core
vertices T.  The script checks that V° carries M(797), finds the type of each core vertex on
V° (copy of a vertex of Sigma_V, constant red, constant blue), and writes the tables:

  vt      type code of core vertex f: t < 21 copies sigma vertex t, 21 constant red, 22 constant blue
  rowR    red rows of the 85 core vertices
  sigR    red rows of M(797) on the 21 sigma vertices
  cst*    the constant-red / constant-blue core positions
  anti    antipodal rows: j with sig (vt j) the antipode of sig (vt i)
  bad*    conflict rows, antipodal pairs removed
  (all tables but vt and rowR are checked against their definitions in Checks.lean)

It also evaluates the finite checks that Checks.lean has the kernel evaluate, with the same
algorithms, and prints a summary (exit 1 if a check fails).  --flip changes edges before
anything else, for negative controls; the output then goes only where --out says.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

EXPECTED_SHA = "07c5cbb696c1d7662870b42e6a1c508e7ef46bf2313f01d297f914e62448867d"
P = 797
NV = 1596
# c0..c9, i0..i9 of r1212-1642, then A_675 (the antipode of i6 = B_675)
SIGMA = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595,
         1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267, 675]
NS = len(SIGMA)
NCORE = 85
CRED, CBLUE = NS, NS + 1


def mathon_red(u, v, sq):
    """M(797): A_x = x, B_x = 797 + x, a = 1594, b = 1595 (as in r1212-1642)."""
    if u == v:
        return 0
    if u > v:
        u, v = v, u
    if v < 2 * P:
        x, y = u % P, v % P
        d = (x - y) % P
        if (u < P) == (v < P):
            return 1 if d and sq[d] else 0
        return 1 if d and not sq[d] else 0
    if u < 2 * P:  # one of a, b
        return 1 if (v == 1594 and u < P) or (v == 1595 and u >= P) else 0
    return 0  # a b


def antipode(v):
    """Graph.lean `antip`: A_x <-> B_x, a <-> b."""
    if v < P:
        return v + P
    if v < 2 * P:
        return v - P
    return 1594 + 1595 - v


def lean_hex(rows, width):
    value = 0
    for i, r in enumerate(rows):
        assert 0 <= r < 1 << width
        value |= r << (width * i)
    return hex(value)


# --- Search.lean's noClique, ported line by line
def log2(x):
    return x.bit_length() - 1


def no_clique(row, t, P_, counter):
    counter[0] += 1
    if t == 0:
        return False
    if P_ == 0:
        return True
    t1 = t - 1
    U, L = P_, 0
    for _ in range(t1):  # colourUnion row t1 P 0
        Q, S, f = U, 0, 256
        while f > 0 and Q != 0:  # greedy row 256 U 0
            v = log2(Q)
            Q, S, f = Q ^ (Q & (row[v] | (1 << v))), S | (1 << v), f - 1
        U, L = U ^ S, L | S
    B = P_ ^ (P_ & L)
    if B == 0:
        return True
    R, f = P_, 256
    while True:  # loopBits
        if f == 0:
            return False
        if B == 0:
            return True
        v = log2(B)
        if not no_clique(row, t1, R & row[v], counter):
            return False
        R, B, f = R ^ (R & (1 << v)), B ^ (1 << v), f - 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("graph")
    ap.add_argument("--out", default=str(Path(__file__).resolve().parent.parent
                                         / "RamseyIncrement" / "R1661" / "Data.lean"))
    ap.add_argument("--flip", action="append", default=[])
    ap.add_argument("--allow-other-sha", action="store_true")
    ap.add_argument("--summary", default=None, help="write the summary JSON here")
    ap.add_argument("--skip-search", action="store_true", help="skip the K12 search")
    ap.add_argument("--no-anti", action="store_true",
                    help="negative control: do not remove the antipodal pairs (anti = 0)")
    args = ap.parse_args()

    raw = Path(args.graph).read_bytes()
    sha = hashlib.sha256(raw).hexdigest()
    if sha != EXPECTED_SHA and not args.allow_other_sha:
        sys.exit(f"unexpected SHA-256 {sha}")
    lines = raw.split(b"\n")
    if lines[-1] != b"" or any(len(l) != len(lines) - 1 for l in lines[:-1]):
        sys.exit("expected n LF-terminated lines of n characters")
    n = len(lines) - 1
    sig_set = set(SIGMA)
    V0 = [v for v in range(NV) if v not in sig_set]
    n0 = len(V0)
    if n != n0 + NCORE:
        sys.exit(f"expected {n0 + NCORE} vertices, got {n}")
    O = [bytearray(c - 48 for c in l) for l in lines[:-1]]
    if any(set(row) - {0, 1} for row in O):
        sys.exit("characters must be 0 or 1")
    for spec in args.flip:
        u, v = map(int, spec.split(":"))
        assert u != v
        O[u][v] ^= 1
        O[v][u] ^= 1
        print(f"FLIPPED {u}-{v}: now {'red' if O[u][v] else 'blue'}")
    for u in range(n):
        if O[u][u]:
            sys.exit("nonzero diagonal")
        for v in range(u):
            if O[u][v] != O[v][u]:
                sys.exit("not symmetric")

    sq = [False] * P
    for x in range(1, P):
        sq[x * x % P] = True
    for i in range(n0):
        row = O[i]
        for j in range(i):
            if row[j] != mathon_red(V0[i], V0[j], sq):
                sys.exit(f"file vertices {i},{j} (M points {V0[i]},{V0[j]}) differ from M(797)")
    print(f"file vertices 0..{n0 - 1}: M(797) on V° (M(797) minus the {NS} sigma vertices)")

    # types of the core vertices on V°
    types = []
    for f in range(NCORE):
        row = O[n0 + f][:n0]
        if all(row):
            types.append(CRED)
        elif not any(row):
            types.append(CBLUE)
        else:
            hits = [t for t, g in enumerate(SIGMA)
                    if all(mathon_red(g, V0[i], sq) == row[i] for i in range(n0))]
            if len(hits) != 1:
                sys.exit(f"core vertex {f}: not a clean type on V° (matches {hits})")
            types.append(hits[0])
    counts = {"copy": sum(t < NS for t in types), "const red": types.count(CRED),
              "const blue": types.count(CBLUE)}
    print("types:", counts)

    full = (1 << NCORE) - 1
    rowR = [sum(O[n0 + i][n0 + j] << j for j in range(NCORE)) for i in range(NCORE)]
    rowB = [full ^ rowR[i] ^ (1 << i) for i in range(NCORE)]
    rowC = {1: rowR, 0: rowB}
    sfull = (1 << NS) - 1
    sigR = [sum(mathon_red(SIGMA[p], SIGMA[q], sq) << q for q in range(NS)) for p in range(NS)]
    sigB = [sfull ^ sigR[p] ^ (1 << p) for p in range(NS)]
    sigC = {1: sigR, 0: sigB}
    anti_pairs = [(p, q) for p in range(NS) for q in range(NS) if SIGMA[q] == antipode(SIGMA[p])]
    print("antipodal sigma pairs (positions):", anti_pairs)

    def bit(x, i):
        return (x >> i) & 1

    def is_nc(j):
        return types[j] < NS

    anti = [sum(1 << j for j in range(NCORE)
                if is_nc(i) and is_nc(j) and SIGMA[types[j]] == antipode(SIGMA[types[i]]))
            for i in range(NCORE)]
    if args.no_anti:
        anti = [0] * NCORE
        print("NO-ANTI: antipodal pairs not removed (NEGATIVE CONTROL)")
    cst = {c: sum(1 << j for j in range(NCORE) if types[j] == (CRED if c else CBLUE))
           for c in (1, 0)}
    rowA = {c: [rowC[c][i] & (full ^ anti[i]) for i in range(NCORE)] for c in (1, 0)}
    bad = {}
    for c in (1, 0):
        rows = []
        for i in range(NCORE):
            r = 0
            for j in range(NCORE):
                if (i != j and is_nc(i) and is_nc(j) and bit(rowC[c][i], j)
                        and not bit(sigC[c][types[i]], types[j]) and not bit(anti[i], j)):
                    r |= 1 << j
            rows.append(r)
        bad[c] = rows

    summary = {"graph_sha256": sha, "flips": args.flip, "no_anti": args.no_anti, "types": types, "type_counts": counts,
               "antipodal_sigma_pairs": anti_pairs}
    ok = True
    for c, name in ((1, "red"), (0, "blue")):
        rc, ra, br, cm = rowC[c], rowA[c], bad[c], cst[c]
        res = {}
        if not args.skip_search:
            counter = [0]
            res["noClique12"] = no_clique(rc, 12, full, counter)
            res["noClique_calls"] = counter[0]
            ok &= res["noClique12"]
        h1 = all(ra[f] & cm == 0 for f in range(NCORE) if bit(cm, f))
        h2 = all(br[u] & ra[f] == 0 for f in range(NCORE) if bit(cm, f)
                 for u in range(NCORE) if bit(ra[f], u))
        h3 = all(br[u] & br[v] == 0 for u in range(NCORE) for v in range(NCORE) if bit(br[u], v))
        h4 = all(br[w] & (ra[u] & ra[v]) == 0 for u in range(NCORE) for v in range(NCORE)
                 if bit(br[u], v) for w in range(NCORE) if bit(ra[u] & ra[v], w))
        nbad = sum(bin(r).count("1") for r in br)
        res.update({"h1": h1, "h2": h2, "h3": h3, "h4": h4, "conflict_ordered_pairs": nbad,
                    "antipodal_ordered_pairs": sum(bin(r).count("1") for r in anti),
                    "constant_vertices": bin(cm).count("1")})
        summary[name] = res
        print(f"[{name}] {res}")
        ok &= h1 and h2 and h3 and h4

    out = Path(args.out)
    src = f"""/-
R(12,12) ≥ 1661: generated by gen/gen_data_1661.py from b1660_PM2.graph; do not edit by hand.
Source SHA-256: {sha}{'' if not args.flip else ' (with flips ' + ' '.join(args.flip) + ': NEGATIVE CONTROL)'}{' (no-anti: NEGATIVE CONTROL)' if args.no_anti else ''}
-/
import RamseyIncrement.R1212.Search

/-!
# The 85-vertex core of the 1660-vertex colouring

Core position `f < 85` is file vertex `1575 + f`.  Sigma positions `0–9` are `c₀,…,c₉`,
`10–19` are `i₀,…,i₉` (the certificates of r1212-1642), and `20` is `A₆₇₅`, the antipode of
`i₆ = B₆₇₅` (`Graph.lean`, `sig`).

`vt` and `rowR` take part in the definition of the colouring (`Graph.lean`).  The other
tables only speed up the checks; `Checks.lean` proves them equal to their definitions.
-/

namespace RamseyIncrement
namespace R1661

/-- The 85 core positions. -/
def mask85 : ℕ := 2 ^ 85 - 1

/-- The 21 sigma positions. -/
def mask21 : ℕ := 2 ^ 21 - 1

/-- Types of the core vertices, `5` bits each: `t < 21` is a copy of sigma vertex `t`,
`21` is constant red, `22` constant blue (towards `V°`). -/
def vtLit : ℕ := {lean_hex(types, 5)}

def vt (f : ℕ) : ℕ := (vtLit >>> (5 * f)) &&& 31

/-- Red rows of the core, `85` bits each: bit `j` of `rowR i` is set iff core vertices
`i` and `j` are joined by a red edge. -/
def rowRLit : ℕ := {lean_hex(rowR, NCORE)}

def rowR (i : ℕ) : ℕ := (rowRLit >>> (85 * i)) &&& mask85

/-- Red rows of `M(797)` on the sigma vertices, `21` bits each. -/
def sigRLit : ℕ := {lean_hex(sigR, NS)}

def sigR (p : ℕ) : ℕ := (sigRLit >>> (21 * p)) &&& mask21

/-- Constant-red core positions. -/
def cstRLit : ℕ := {hex(cst[1])}

/-- Constant-blue core positions. -/
def cstBLit : ℕ := {hex(cst[0])}

/-- Antipodal rows, `85` bits each. -/
def antiLit : ℕ := {lean_hex(anti, NCORE)}

/-- Red conflict rows, `85` bits each. -/
def badRLit : ℕ := {lean_hex(bad[1], NCORE)}

/-- Blue conflict rows, `85` bits each. -/
def badBLit : ℕ := {lean_hex(bad[0], NCORE)}

end R1661
end RamseyIncrement
"""
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(src.encode("utf-8"))
    summary["output"] = str(out)
    summary["output_sha256"] = hashlib.sha256(src.encode("utf-8")).hexdigest()
    summary["all_checks_pass"] = bool(ok)
    print("wrote", out, summary["output_sha256"])
    if args.summary:
        Path(args.summary).write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
    print("CHECKS:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
