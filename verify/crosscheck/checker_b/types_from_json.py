"""Write the TYPES file read by checker B (xcheck.c) from the description of the colouring in
graph/r1212_1660.json.  Needs only the Python standard library.

usage: python3 types_from_json.py graph/r1212_1660.json > r1212_1660.types

The TYPES file has a first line "SIGMA k g1 .. gk", then one line per file vertex, in order:
"V m" for the vertex m of M(797) in V0, or "T g" / "T R" / "T B" for a core vertex that copies
g in Sigma_V, is constant red or is constant blue.  These are only the declared types; xcheck
checks every edge of the file against them."""
import json
import sys

meta = json.load(open(sys.argv[1]))
sig = [int(g) for g in meta["Sigma_V"]["vertices"]]
names = meta["Sigma_V"]["names"]
n, n0 = int(meta["n"]), int(meta["V0"]["size"])
V0 = [v for v in range(1596) if v not in set(sig)]
assert len(V0) == n0 and meta["V0"]["file_vertices"] == [0, n0 - 1]
core = sorted(meta["core_vertices"], key=lambda e: int(e["vertex"]))
assert [int(e["vertex"]) for e in core] == list(range(n0, n))
lines = ["SIGMA %d %s" % (len(sig), " ".join(map(str, sig)))]
lines += ["V %d" % m for m in V0]  # file vertex v < |V0| is the v-th vertex of M(797) outside Sigma_V
for e in core:
    if e["type"] == "copy":
        g = int(e["of_vertex"])
        assert names[sig.index(g)] == e["of"], e
        lines.append("T %d" % g)
    else:
        lines.append("T " + {"constant red": "R", "constant blue": "B"}[e["type"]])
sys.stdout.write("\n".join(lines) + "\n")
