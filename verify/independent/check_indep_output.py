"""Check the output of indep_kclique against its graph (written for the audit, 2026-11-03).

Passes when: the graph is n LF-terminated rows of n characters 0/1, symmetric with zero diagonal;
every output line is a complete JSON object; the tasks are exactly {(v,c) : 0 <= v < n, c = 0,1},
each once; each task's rank and m agree with the ranks and |L(v,c)| recomputed here; and every
result is "none".

usage: python3.14 check_indep_output.py GRAPH JSONL
"""
import hashlib
import json
import sys

import numpy as np

graph, jsonl = sys.argv[1], sys.argv[2]
raw = open(graph, 'rb').read()
lines = raw.split(b'\n')
n = len(lines) - 1
assert lines[-1] == b'' and all(len(r) == n and set(r) <= {48, 49} for r in lines[:-1]), 'format'
R = (np.frombuffer(b''.join(lines[:-1]), dtype=np.uint8).reshape(n, n) - 48).astype(np.int64)
assert (R == R.T).all() and not R.diagonal().any(), 'symmetry/diagonal'
print(f'graph n={n} sha256 {hashlib.sha256(raw).hexdigest()}')
problems = []
rank, size = {}, {}
for c in (0, 1):
    A = R if c == 1 else 1 - R - np.eye(n, dtype=np.int64)
    deg = A.sum(1)
    gone = np.zeros(n, bool)
    rk = np.zeros(n, int)
    for step in range(n):
        v = int(np.argmin(np.where(gone, 1 << 40, deg)))   # first minimum = smallest index
        rk[v], gone[v] = step, True
        deg = deg - A[v]
    rank[c] = rk
    later = rk[None, :] > rk[:, None]
    size[c] = (A.astype(bool) & later).sum(1)
text = open(jsonl, 'rb').read()
if not text.endswith(b'\n'):
    problems.append('last line incomplete')
recs = {}
for k, line in enumerate(text.split(b'\n')[:-1], 1):
    try:
        r = json.loads(line)
    except ValueError:
        problems.append(f'line {k} is not JSON')
        continue
    key = (r['v'], r['c'])
    if key in recs:
        problems.append(f'task {key} twice')
    recs[key] = r
expected = {(v, c) for v in range(n) for c in (0, 1)}
if set(recs) != expected:
    problems.append(f'task set: {len(expected - set(recs))} missing, {len(set(recs) - expected)} extra')
results = {}
for (v, c), r in recs.items():
    if (v, c) not in expected:
        continue
    if r['rank'] != rank[c][v] or r['m'] != size[c][v]:
        problems.append(f'task {(v, c)}: rank/m {r["rank"]}/{r["m"]}, recomputed {rank[c][v]}/{size[c][v]}')
    results[r['result']] = results.get(r['result'], 0) + 1
    if r['result'] != 'none':
        problems.append(f'task {(v, c)}: {r["result"]} {r.get("witness")}')
cpu = sum(r['sec'] for r in recs.values()) / 3600
nodes = sum(r['nodes'] for r in recs.values())
big = max(recs.values(), key=lambda r: r['m'])
slow = max(recs.values(), key=lambda r: r['sec'])
print(f'tasks {len(recs)} of {len(expected)}; results {results}; nodes {nodes}; cpu {cpu:.2f} h')
print(f'largest task m={big["m"]} (v={big["v"]}, c={big["c"]}); slowest {slow["sec"]} s (v={slow["v"]}, c={slow["c"]})')
for p in problems[:20]:
    print('PROBLEM:', p)
print('RESULT: every task "none", all tasks present' if not problems else f'{len(problems)} problems')
print('CHECK:', 'PASS' if not problems else 'FAIL')
sys.exit(1 if problems else 0)
