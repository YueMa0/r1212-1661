/* indep_kclique.c -- an independent exhaustive check that a 2-coloured complete graph has no
 * monochromatic K_t.  Written for the audit of r1212-1658 (2026-11-03) without reusing code from
 * verify/bruteforce_kclique.c; it also splits the problem differently.
 *
 * Input: n lines of n characters '0'/'1', LF-terminated; character w of line v is 1 iff vw is red.
 * The file must be symmetric with a zero diagonal (checked).
 *
 * Decomposition.  For each colour c, rank the vertices by removing, one at a time, a vertex of
 * minimum degree in the colour-c graph of the vertices not yet removed (ties: smallest index);
 * rank_c(v) is the step at which v is removed.  A monochromatic K_t of colour c has a unique
 * vertex v of smallest rank_c; its other t-1 vertices lie in
 *     L(v,c) = { w : colour(v,w) = c, rank_c(w) > rank_c(v) }
 * and form a colour-c K_{t-1} there.  So the graph has no monochromatic K_t iff no task (v,c)
 * finds a colour-c K_{t-1} in L(v,c).  |L(v,c)| is the degree of v when it is removed, so the
 * largest task is the degeneracy of the colour-c graph.  (bruteforce_kclique.c uses the file
 * order instead, so the two programs solve different subproblems.)
 *
 * Search: has_clique(P, k) decides whether the vertex set P contains a k-clique.
 *   - Colour P greedily with k-1 classes (independent sets).  A clique meets each class at most
 *     once, so every k-clique of P contains a vertex of B = the vertices left uncoloured.
 *   - If B is empty there is no k-clique.  Otherwise take the vertices b of B one at a time:
 *     search for a (k-1)-clique in P n N(b), then delete b from P.  A k-clique whose first vertex
 *     of B (in this order) is b avoids the earlier ones, so it is found in the branch of b.
 * The vertices of L(v,c) are renumbered in smallest-last (degeneracy) order first; this only
 * affects speed.
 *
 * Output: one JSON line per task: v, c, rank, m = |L(v,c)|, result "none" or "found", nodes, sec,
 * and for "found" a witness (t vertices, v last), re-checked against the input.
 *
 * usage: indep_kclique GRAPH t OUT threads [v_lo v_hi]
 */
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXT 64

static int n, t;
static unsigned char *col; /* col[u*n+w] = 1 if red */
static int rank_of[2][MAXN];
static FILE *out;
static pthread_mutex_t out_mx = PTHREAD_MUTEX_INITIALIZER;

typedef struct { int v, c, m; } task_t;
static task_t *tasks;
static int ntasks;
static atomic_int next_task, n_found;

typedef struct {
    int m, nw;
    uint64_t (*adj)[MAXW]; /* local adjacency, m rows */
    int loc2glob[MAXN];
    long long nodes;
    int stack[MAXT], found, wit[MAXT];
} search_t;

static inline int first_bit(const uint64_t *s, int nw) {
    for (int i = 0; i < nw; i++)
        if (s[i]) return 64 * i + __builtin_ctzll(s[i]);
    return -1;
}

static inline int last_bit(const uint64_t *s, int nw) {
    for (int i = nw - 1; i >= 0; i--)
        if (s[i]) return 64 * i + 63 - __builtin_clzll(s[i]);
    return -1;
}

static inline int popcnt(const uint64_t *s, int nw) {
    int k = 0;
    for (int i = 0; i < nw; i++) k += __builtin_popcountll(s[i]);
    return k;
}

/* Does P contain a k-clique?  depth = number of vertices already on the stack. */
static int has_clique(search_t *S, uint64_t *P, int k, int depth) {
    int nw = S->nw;
    S->nodes++;
    if (k == 0) {
        S->found = 1;
        memcpy(S->wit, S->stack, sizeof(int) * depth);
        return 1;
    }
    int any = first_bit(P, nw);
    if (any < 0) return 0;
    if (k == 1) {
        S->stack[depth] = any;
        S->found = 1;
        memcpy(S->wit, S->stack, sizeof(int) * (depth + 1));
        return 1;
    }
    /* B = P minus k-1 greedy colour classes */
    uint64_t B[MAXW], Q[MAXW];
    memcpy(B, P, sizeof(uint64_t) * nw);
    for (int cls = 0; cls < k - 1; cls++) {
        memcpy(Q, B, sizeof(uint64_t) * nw);
        int u;
        while ((u = first_bit(Q, nw)) >= 0) {
            B[u >> 6] &= ~(1ULL << (u & 63)); /* u joins this class */
            for (int i = 0; i < nw; i++) Q[i] &= ~S->adj[u][i];
            Q[u >> 6] &= ~(1ULL << (u & 63));
        }
        if (first_bit(B, nw) < 0) return 0; /* P is (cls+1)-colourable, cls+1 <= k-1 */
    }
    /* branch on the vertices of B, last one first */
    uint64_t NP[MAXW];
    int b;
    while ((b = last_bit(B, nw)) >= 0) {
        B[b >> 6] &= ~(1ULL << (b & 63));
        for (int i = 0; i < nw; i++) NP[i] = P[i] & S->adj[b][i];
        if (popcnt(NP, nw) >= k - 1) {
            S->stack[depth] = b;
            if (has_clique(S, NP, k - 1, depth + 1)) return 1;
        }
        P[b >> 6] &= ~(1ULL << (b & 63));
    }
    return 0;
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void run_task(search_t *S, const task_t *T) {
    int v = T->v, c = T->c, m = 0;
    static _Thread_local int mem[MAXN], deg[MAXN], removed[MAXN], order[MAXN];
    for (int w = 0; w < n; w++)
        if (w != v && col[(size_t)v * n + w] == c && rank_of[c][w] > rank_of[c][v]) mem[m++] = w;
    if (m != T->m) { fprintf(stderr, "internal error: task size\n"); exit(3); }
    /* smallest-last order: repeatedly remove a vertex of minimum remaining degree */
    for (int i = 0; i < m; i++) {
        deg[i] = 0;
        removed[i] = 0;
        for (int j = 0; j < m; j++)
            if (j != i && col[(size_t)mem[i] * n + mem[j]] == c) deg[i]++;
    }
    for (int pos = m - 1; pos >= 0; pos--) {
        int best = -1;
        for (int i = 0; i < m; i++)
            if (!removed[i] && (best < 0 || deg[i] < deg[best])) best = i;
        removed[best] = 1;
        order[pos] = best;
        for (int j = 0; j < m; j++)
            if (!removed[j] && col[(size_t)mem[best] * n + mem[j]] == c) deg[j]--;
    }
    S->m = m;
    S->nw = (m + 63) / 64 ? (m + 63) / 64 : 1;
    for (int i = 0; i < m; i++) S->loc2glob[i] = mem[order[i]];
    for (int i = 0; i < m; i++) {
        memset(S->adj[i], 0, sizeof(uint64_t) * S->nw);
        for (int j = 0; j < m; j++)
            if (j != i && col[(size_t)S->loc2glob[i] * n + S->loc2glob[j]] == c)
                S->adj[i][j >> 6] |= 1ULL << (j & 63);
    }
    S->nodes = 0;
    S->found = 0;
    double t0 = now();
    uint64_t P[MAXW];
    memset(P, 0, sizeof P);
    for (int i = 0; i < m; i++) P[i >> 6] |= 1ULL << (i & 63);
    int found = has_clique(S, P, t - 1, 0);
    double sec = now() - t0;
    char extra[2048] = "";
    if (found) {
        int g[MAXT], ok = 1, len = 0;
        for (int i = 0; i < t - 1; i++) g[i] = S->loc2glob[S->wit[i]];
        g[t - 1] = v;
        for (int i = 0; i < t; i++)
            for (int j = i + 1; j < t; j++)
                if (g[i] == g[j] || col[(size_t)g[i] * n + g[j]] != c) ok = 0;
        for (int i = 0; i < t - 1; i++)
            if (rank_of[c][g[i]] <= rank_of[c][v]) ok = 0;
        len += snprintf(extra + len, sizeof extra - len, ",\"witness_ok\":%s,\"witness\":[", ok ? "true" : "false");
        for (int i = 0; i < t; i++) len += snprintf(extra + len, sizeof extra - len, "%s%d", i ? "," : "", g[i]);
        snprintf(extra + len, sizeof extra - len, "]");
        atomic_fetch_add(&n_found, 1);
    }
    pthread_mutex_lock(&out_mx);
    fprintf(out, "{\"v\":%d,\"c\":%d,\"rank\":%d,\"m\":%d,\"result\":\"%s\",\"nodes\":%lld,\"sec\":%.3f%s}\n",
            v, c, rank_of[c][v], m, found ? "found" : "none", S->nodes, sec, extra);
    fflush(out);
    pthread_mutex_unlock(&out_mx);
}

static void *worker(void *arg) {
    (void)arg;
    search_t *S = calloc(1, sizeof(search_t));
    S->adj = malloc(sizeof(uint64_t) * MAXW * MAXN);
    if (!S || !S->adj) { fprintf(stderr, "out of memory\n"); exit(3); }
    for (;;) {
        int i = atomic_fetch_add(&next_task, 1);
        if (i >= ntasks) break;
        run_task(S, &tasks[i]);
    }
    free(S->adj);
    free(S);
    return NULL;
}

static int by_size_desc(const void *a, const void *b) {
    const task_t *p = a, *q = b;
    if (p->m != q->m) return q->m - p->m;
    if (p->v != q->v) return p->v - q->v;
    return p->c - q->c;
}

static void die(const char *msg) {
    fprintf(stderr, "input error: %s\n", msg);
    exit(2);
}

int main(int argc, char **argv) {
    if (argc != 5 && argc != 7) {
        fprintf(stderr, "usage: %s GRAPH t OUT threads [v_lo v_hi]\n", argv[0]);
        return 2;
    }
    t = atoi(argv[2]);
    int threads = atoi(argv[4]);
    if (t < 2 || t > MAXT || threads < 1 || threads > 256) die("bad t or thread count");
    /* strict read: n rows, each exactly n characters 0/1 followed by LF */
    FILE *f = fopen(argv[1], "rb");
    if (!f) die("cannot open graph");
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = malloc(size + 1);
    if (fread(buf, 1, size, f) != (size_t)size) die("short read");
    fclose(f);
    char *nl = memchr(buf, '\n', size);
    if (!nl) die("no LF");
    n = (int)(nl - buf);
    if (n < 1 || n > MAXN) die("bad n");
    if (size != (long)n * (n + 1)) die("file size is not n*(n+1)");
    col = malloc((size_t)n * n);
    for (int i = 0; i < n; i++) {
        const char *row = buf + (size_t)i * (n + 1);
        if (row[n] != '\n') die("row not LF-terminated at length n");
        for (int j = 0; j < n; j++) {
            if (row[j] != '0' && row[j] != '1') die("character other than 0/1");
            col[(size_t)i * n + j] = row[j] == '1';
        }
    }
    free(buf);
    for (int i = 0; i < n; i++) {
        if (col[(size_t)i * n + i]) die("nonzero diagonal");
        for (int j = i + 1; j < n; j++)
            if (col[(size_t)i * n + j] != col[(size_t)j * n + i]) die("not symmetric");
    }
    int vlo = argc == 7 ? atoi(argv[5]) : 0, vhi = argc == 7 ? atoi(argv[6]) : n;
    if (vlo < 0 || vhi > n || vlo > vhi) die("bad v range");
    /* rank_c: smallest-degree-first removal order of the colour-c graph */
    {
        int *deg = malloc(sizeof(int) * n), *gone = calloc(n, sizeof(int)), *seen = calloc(n, sizeof(int));
        for (int c = 0; c < 2; c++) {
            for (int i = 0; i < n; i++) {
                deg[i] = 0;
                gone[i] = 0;
                seen[i] = 0;
                for (int j = 0; j < n; j++)
                    if (j != i && col[(size_t)i * n + j] == c) deg[i]++;
            }
            for (int step = 0; step < n; step++) {
                int best = -1;
                for (int i = 0; i < n; i++)
                    if (!gone[i] && (best < 0 || deg[i] < deg[best])) best = i;
                gone[best] = 1;
                rank_of[c][best] = step;
                for (int j = 0; j < n; j++)
                    if (!gone[j] && j != best && col[(size_t)best * n + j] == c) deg[j]--;
            }
            for (int i = 0; i < n; i++) seen[rank_of[c][i]]++;
            for (int i = 0; i < n; i++)
                if (seen[i] != 1) die("internal error: ranks are not a permutation");
        }
        free(deg);
        free(gone);
        free(seen);
    }
    tasks = malloc(sizeof(task_t) * 2 * n);
    for (int v = vlo; v < vhi; v++)
        for (int c = 0; c < 2; c++) {
            int m = 0;
            for (int w = 0; w < n; w++)
                m += w != v && col[(size_t)v * n + w] == c && rank_of[c][w] > rank_of[c][v];
            tasks[ntasks++] = (task_t){v, c, m};
        }
    qsort(tasks, ntasks, sizeof(task_t), by_size_desc);
    out = fopen(argv[3], "wx"); /* refuse to overwrite or append */
    if (!out) die("cannot create OUT (it must not exist yet)");
    fprintf(stderr, "n=%d t=%d tasks=%d threads=%d\n", n, t, ntasks, threads);
    pthread_t th[256];
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, 16 << 20);
    for (int i = 0; i < threads; i++) pthread_create(&th[i], &attr, worker, NULL);
    for (int i = 0; i < threads; i++) pthread_join(th[i], NULL);
    fclose(out);
    fprintf(stderr, "finished: tasks=%d found=%d\n", ntasks, atomic_load(&n_found));
    return 0;
}
