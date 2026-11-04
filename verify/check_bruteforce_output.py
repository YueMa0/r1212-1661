#!/usr/bin/env python3
"""Check the output of bruteforce_kclique against its graph.  Standard library only.

usage: check_bruteforce_output.py GRAPH JSONL [--t 12] [--vrange LO HI]
           [--reference REF.jsonl] [--spec controls.json --name NAME]

GRAPH is the text file (n lines of n characters 0/1, 1 = red) or its .gz.  The check passes when
  - the graph is symmetric with a zero diagonal;
  - every line of JSONL is one complete JSON object with v, c, m, result, nodes and sec;
  - the tasks are exactly {(v, c) : LO <= v < HI, c = 0, 1}, each once (default LO = 0, HI = n);
  - each m equals |{w > v : colour(v, w) = c}| in the graph;
  - every result is "none", except the tasks the spec expects to be "found"; each of those has
    witness_ok true and a witness of t distinct vertices, v first and the others later than v,
    all pairs of colour c in the graph;
  - with --reference: m, result and nodes equal those of the same task in REF.jsonl;
  - with --spec: the graph text has the spec's SHA-256, and it differs from the spec's base graph
    (looked up next to GRAPH) only on pairs inside the planted vertex set.
Prints CHECK: PASS or CHECK: FAIL and exits with 0 or 1.
"""
import argparse
import gzip
import hashlib
import json
import os
import sys

REQUIRED = ('v', 'c', 'm', 'result', 'nodes', 'sec')


def read_graph(path):
    with open(path, 'rb') as f:
        raw = f.read()
    if path.endswith('.gz'):
        raw = gzip.decompress(raw)
    lines = raw.split(b'\n')
    n = len(lines) - 1
    if lines[-1] != b'' or any(len(r) != n or r.strip(b'01') for r in lines[:-1]):
        raise SystemExit(f'CHECK: FAIL\n{path}: expected n LF-terminated rows of n characters 0/1')
    rows = lines[:-1]
    if [bytes(col) for col in zip(*rows)] != rows or any(rows[i][i] != 48 for i in range(n)):
        raise SystemExit(f'CHECK: FAIL\n{path}: not symmetric with a zero diagonal')
    return rows, hashlib.sha256(raw).hexdigest()


def read_jsonl(path, problems):
    with open(path, 'rb') as f:
        text = f.read()
    lines = text.split(b'\n')
    if lines[-1] == b'':
        lines.pop()
    elif text:
        problems.append(f'{path}: the last line is incomplete (no newline at the end)')
    recs = []
    for k, line in enumerate(lines, 1):
        try:
            r = json.loads(line)
        except ValueError:
            problems.append(f'{path} line {k}: not a JSON object: {line[:80]!r}')
            continue
        if not isinstance(r, dict) or any(key not in r for key in REQUIRED):
            problems.append(f'{path} line {k}: missing fields: {line[:80]!r}')
            continue
        recs.append(r)
    return recs


def witness_problem(rows, rec, t):
    w, v, c = rec.get('witness'), rec['v'], rec['c']
    if (rec.get('witness_ok') is not True or not isinstance(w, list) or len(w) != t
            or not all(isinstance(x, int) for x in w)):
        return f'witness_ok not true, or the witness is not {t} integers'
    if len(set(w)) != t or w[0] != v or not all(v < x < len(rows) for x in w[1:]):
        return f'witness is not v followed by {t - 1} distinct later vertices: {w}'
    bad = [(a, b) for i, a in enumerate(w) for b in w[i + 1:] if rows[a][b] != 48 + c]
    return f'witness pairs not of colour {c}: {bad[:5]}' if bad else None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('graph')
    ap.add_argument('jsonl')
    ap.add_argument('--t', type=int, default=12)
    ap.add_argument('--vrange', type=int, nargs=2, metavar=('LO', 'HI'))
    ap.add_argument('--reference')
    ap.add_argument('--spec')
    ap.add_argument('--name')
    args = ap.parse_args()
    problems = []
    rows, text_sha = read_graph(args.graph)
    n = len(rows)
    print(f'graph {os.path.basename(args.graph)}: n = {n}, text sha256 {text_sha}')
    expect_found, lo, hi = set(), 0, n
    if args.spec:
        with open(args.spec, encoding='utf-8') as f:
            spec = json.load(f)[args.name]
        lo, hi = spec['vrange']
        expect_found = {tuple(x) for x in spec['expect_found']}
        if text_sha != spec['text_sha256']:
            problems.append(f'graph text sha256 differs from the spec ({spec["text_sha256"]})')
        base, _ = read_graph(os.path.join(os.path.dirname(args.graph) or '.', spec['base']))
        planted = set(spec['planted'])
        diff = [(i, j) for i in range(n) if rows[i] != base[i] for j in range(i + 1, n) if rows[i][j] != base[i][j]]
        outside = [p for p in diff if not set(p) <= planted]
        print(f'spec {args.name}: {len(diff)} pairs differ from {spec["base"]}, all inside the planted set: {not outside}')
        if outside:
            problems.append(f'pairs outside the planted set differ from the base graph: {outside[:5]}')
    if args.vrange:
        lo, hi = args.vrange
    expected = {(v, c) for v in range(lo, hi) for c in (0, 1)}
    recs = read_jsonl(args.jsonl, problems)
    seen = {}
    for r in recs:
        key = (r['v'], r['c'])
        if key in seen:
            problems.append(f'task {key} appears more than once')
        seen[key] = r
    missing, extra = sorted(expected - set(seen)), sorted(set(seen) - expected)
    if missing:
        problems.append(f'{len(missing)} tasks missing, first {missing[:5]}')
    if extra:
        problems.append(f'{len(extra)} tasks outside the expected range, first {extra[:5]}')
    ref = {}
    if args.reference:
        for r in read_jsonl(args.reference, problems):
            ref[(r['v'], r['c'])] = r
    counts, real = {}, []
    for key in sorted(set(seen) & expected):
        r = seen[key]
        v, c = key
        tail = rows[v][v + 1:]
        red = tail.count(b'1')
        m = red if c == 1 else len(tail) - red
        if r['m'] != m:
            problems.append(f'task {key}: m = {r["m"]}, but the graph gives {m}')
        counts[r['result']] = counts.get(r['result'], 0) + 1
        if r['result'] == 'found':
            why = witness_problem(rows, r, args.t)
            if why is None:
                real.append((key, r['witness']))
            if key not in expect_found:
                problems.append(f'task {key}: unexpected "found" ({"valid witness" if why is None else why})')
            elif why:
                problems.append(f'task {key}: {why}')
        elif key in expect_found:
            problems.append(f'task {key}: expected "found", got "{r["result"]}"')
        elif r['result'] != 'none':
            problems.append(f'task {key}: result "{r["result"]}"')
        if args.reference:
            q = ref.get(key)
            if q is None:
                problems.append(f'task {key}: not in the reference')
            elif (q['m'], q['result'], q['nodes']) != (r['m'], r['result'], r['nodes']):
                problems.append(f'task {key}: (m, result, nodes) = {(r["m"], r["result"], r["nodes"])}, '
                                f'reference {(q["m"], q["result"], q["nodes"])}')
    sec = [r['sec'] for r in recs]
    nodes = sum(r['nodes'] for r in recs)
    longest = max(recs, key=lambda r: r['sec']) if recs else None
    print(f'tasks expected {len(expected)}, recorded {len(recs)}; results {dict(sorted(counts.items()))}')
    if recs:
        print(f'nodes {nodes}; cpu {sum(sec) / 3600:.2f} h; longest task {longest["sec"]} s '
              f'(v = {longest["v"]}, c = {longest["c"]}, m = {longest["m"]})')
    if args.reference:
        print(f'reference {os.path.basename(args.reference)}: compared m, result and nodes task by task')
    for key, w in real:
        print(f'monochromatic K{args.t} in colour {key[1]} (1 = red): {w}')
    for p in problems[:20]:
        print('PROBLEM:', p)
    if len(problems) > 20:
        print(f'PROBLEM: ... and {len(problems) - 20} more')
    if not problems and not expect_found and (lo, hi) == (0, n):
        print(f'RESULT: no monochromatic K{args.t} (every task "none", all {len(expected)} tasks present)')
    elif not problems and expect_found:
        print(f'RESULT: the planted K{args.t} was found with a valid witness; all other tasks "none"')
    print('CHECK:', 'FAIL' if problems else 'PASS')
    sys.exit(1 if problems else 0)


if __name__ == '__main__':
    main()
