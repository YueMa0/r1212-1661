"""Compare the Lean definition of the 1660-vertex colouring with b1660_PM2.graph.

    python -B tools/compare_export_1661.py GRAPH [--summary PATH]

1. Rebuild the whole colouring from RamseyIncrement/R1661/Data.lean (its literals parsed here,
   not taken from gen_data_1661.py) and the sigma list of RamseyIncrement/R1661/Graph.lean
   (`sig`, parsed here), following Graph.lean case by case, and compare every byte with GRAPH.
   File vertex `v < 1575` is `inl` of the `v`-th vertex of `M(797)` outside `Σ_V` (in the
   order of r1212-1642); file vertex `1575 + f` is `inr f`.
2. If present, compare the rows that Export1661.lean wrote with Lean's interpreter
   (build/export/rows_1661_from_lean.txt, rows `i:bits`) with the same rows of GRAPH.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
P = 797
NCORE = 85


def lit(src, name):
    return int(re.search(rf"def {name} : ℕ := (0x[0-9a-f]+)", src).group(1), 16)


def parse_sig(graph_src):
    """`def sig : Fin 21 → MV := ![B 133, ..., b, ..., a, ..., A 675]` -> file numbering."""
    body = re.search(r"def sig : Fin 21 → MV :=\s*!\[(.*?)\]", graph_src, re.S).group(1)
    out = []
    for tok in (t.strip() for t in body.split(",")):
        if tok == "a":
            out.append(1594)
        elif tok == "b":
            out.append(1595)
        else:
            kind, x = tok.split()
            assert kind in "AB" and 0 <= int(x) < P, tok
            out.append(int(x) + (P if kind == "B" else 0))
    assert len(out) == 21 and len(set(out)) == 21
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("graph")
    ap.add_argument("--summary", default=None)
    args = ap.parse_args()
    raw = Path(args.graph).read_bytes()
    rows = raw.split(b"\n")[:-1]
    n = len(rows)
    out = {"graph_sha256": hashlib.sha256(raw).hexdigest(), "n": n}

    data = (ROOT / "RamseyIncrement" / "R1661" / "Data.lean").read_text(encoding="utf-8")
    graph = (ROOT / "RamseyIncrement" / "R1661" / "Graph.lean").read_text(encoding="utf-8")
    out["data_lean_sha256"] = hashlib.sha256(data.encode("utf-8")).hexdigest()
    out["graph_lean_sha256"] = hashlib.sha256(graph.encode("utf-8")).hexdigest()
    sig = parse_sig(graph)
    out["sigma_file_numbering"] = sig
    vt_lit, row_lit = lit(data, "vtLit"), lit(data, "rowRLit")
    vt = [(vt_lit >> (5 * f)) & 31 for f in range(NCORE)]
    rowR = [(row_lit >> (NCORE * i)) & ((1 << NCORE) - 1) for i in range(NCORE)]
    sq = {x * x % P for x in range(1, P)}
    V0 = [v for v in range(2 * P + 2) if v not in set(sig)]
    n0 = len(V0)
    if n != n0 + NCORE:
        sys.exit(f"expected {n0 + NCORE} vertices, got {n}")

    def mv(v):  # file numbering of M(797) -> M(797) vertex
        return ("A", v) if v < P else ("B", v - P) if v < 2 * P else ("a",) if v == 1594 else ("b",)

    def mathon(u, v):  # Mathon.lean `mathonAdj`
        if u == v:
            return 0
        ku, kv = u[0], v[0]
        if ku in "AB" and kv in "AB":
            d = (u[1] - v[1]) % P
            if ku == kv:
                return int(d in sq)
            return int(d != 0 and d not in sq)
        return int({ku, kv} in ({"A", "a"}, {"B", "b"}))

    def type_adj(t, u):  # Graph.lean `typeAdj`
        return mathon(mv(sig[t]), u) if t < 21 else int(t == 21)

    def adj(x, y):  # Graph.lean `adjW`
        if x < n0 and y < n0:
            return mathon(mv(V0[x]), mv(V0[y]))
        if x >= n0 and y >= n0:
            f, g = x - n0, y - n0
            return int(f != g and (rowR[f] >> g) & 1)
        u, f = (x, y - n0) if x < n0 else (y, x - n0)
        return type_adj(vt[f], mv(V0[u]))

    bad = []
    for i in range(n):
        rebuilt = bytes(48 + adj(i, j) for j in range(n))
        if rebuilt != rows[i]:
            j = next(k for k in range(n) if rebuilt[k] != rows[i][k])
            bad.append((i, j))
            if len(bad) >= 5:
                break
    out["rebuild_from_data_lean"] = {"pairs": n * n, "first_differences": bad,
                                     "identical": not bad}
    print(f"rebuild from Data.lean + Graph.lean ({n} x {n}):",
          "IDENTICAL" if not bad else f"DIFFERS at {bad}")

    lean_rows = ROOT / "build" / "export" / "rows_1661_from_lean.txt"
    if lean_rows.is_file():
        lines = lean_rows.read_bytes().split(b"\n")[:-1]
        ok, diff = 0, []
        for line in lines:
            i, bits = line.split(b":")
            i = int(i)
            if bits == rows[i]:
                ok += 1
            else:
                diff.append(i)
        out["lean_interpreter_rows"] = {
            "file_sha256": hashlib.sha256(lean_rows.read_bytes()).hexdigest(),
            "rows": len(lines), "row_indices": [int(l.split(b":")[0]) for l in lines],
            "identical_rows": ok, "differing_rows": diff}
        print(f"Lean interpreter rows: {ok}/{len(lines)} identical; differing {diff}")
    if args.summary:
        Path(args.summary).write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    good = out["rebuild_from_data_lean"]["identical"] and not out.get(
        "lean_interpreter_rows", {}).get("differing_rows")
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
