/* Exhaustive check that a 2-coloured complete graph has no monochromatic K_t.
 *
 * Every monochromatic K_t has a unique smallest vertex v; the other t-1 vertices are later
 * vertices of colour c to v.  So for every v and colour c we decide whether
 *     P(v,c) = { w > v : colour(v,w) = c }
 * contains a colour-c clique of size t-1.  Each (v,c) is one task.  The search is an exact
 * bitset branch and bound (MCQ style: greedy colouring bound, degree-ordered vertices).
 * No structure of the graph is used.
 *
 * Input: n lines of n characters '0'/'1' (char w of line v = 1 iff vw is red).
 * Output: one JSON line per finished task, appended to OUT; finished tasks are skipped on restart.
 * Result "none" = complete search, no clique; "found" = witness (re-checked); "timeout" = node cap hit.
 *
 * usage: bruteforce_kclique GRAPH t OUT threads [node_cap] [v_lo v_hi]
 */
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXM 1024
#define MW (MAXM / 64)

static int n, T;
static unsigned char *A;
static long long node_cap;
static FILE *out;
static pthread_mutex_t out_mx = PTHREAD_MUTEX_INITIALIZER;
typedef struct { int v, c, m; } task_t;
static task_t *tasks;
static int ntasks;
static atomic_int next_task;
static atomic_int n_found, n_timeout;

typedef struct {
    int m, nw, target, found, aborted;
    long long nodes;
    int glob[MAXM], cur[64], wit[64];
    uint64_t adj[MAXM][MW];
} ctx_t;

static inline int lowest(const uint64_t *s, int nw) {
    for (int i = 0; i < nw; i++)
        if (s[i]) return i * 64 + __builtin_ctzll(s[i]);
    return -1;
}

static void expand(ctx_t *x, uint64_t *P, int depth) {
    int16_t order[MAXM], col[MAXM];
    uint64_t U[MW], Q[MW], NP[MW];
    int nw = x->nw, cnt = 0, k = 0, v;
    if (x->found || x->aborted) return;
    if (node_cap && ++x->nodes > node_cap) { x->aborted = 1; return; }
    if (!node_cap) x->nodes++;
    memcpy(U, P, sizeof(uint64_t) * nw);
    while (lowest(U, nw) >= 0) {
        k++;
        memcpy(Q, U, sizeof(uint64_t) * nw);
        while ((v = lowest(Q, nw)) >= 0) {
            Q[v >> 6] &= ~(1ULL << (v & 63));
            U[v >> 6] &= ~(1ULL << (v & 63));
            for (int i = 0; i < nw; i++) Q[i] &= ~x->adj[v][i];
            order[cnt] = (int16_t)v;
            col[cnt++] = (int16_t)k;
        }
    }
    for (int i = cnt - 1; i >= 0; i--) {
        if (depth + col[i] < x->target) return;
        v = order[i];
        x->cur[depth] = v;
        if (depth + 1 == x->target) {
            x->found = 1;
            memcpy(x->wit, x->cur, sizeof(int) * x->target);
            return;
        }
        int any = 0;
        for (int j = 0; j < nw; j++) any |= (NP[j] = P[j] & x->adj[v][j]) != 0;
        if (any) {
            expand(x, NP, depth + 1);
            if (x->found || x->aborted) return;
        }
        P[v >> 6] &= ~(1ULL << (v & 63));
    }
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int col_of(int u, int w) { return A[(size_t)u * n + w]; }

static void run_task(ctx_t *x, const task_t *t) {
    int v = t->v, c = t->c, m = 0;
    int deg[MAXM], idx[MAXM];
    for (int w = v + 1; w < n; w++)
        if (col_of(v, w) == c) idx[m++] = w;
    /* order by degree inside P, descending */
    for (int i = 0; i < m; i++) {
        deg[i] = 0;
        for (int j = 0; j < m; j++)
            if (j != i && col_of(idx[i], idx[j]) == c) deg[i]++;
    }
    int ord[MAXM];
    for (int i = 0; i < m; i++) ord[i] = i;
    for (int i = 1; i < m; i++) {            /* insertion sort, m <= 1024 */
        int a = ord[i], j = i - 1;
        while (j >= 0 && deg[ord[j]] < deg[a]) { ord[j + 1] = ord[j]; j--; }
        ord[j + 1] = a;
    }
    x->m = m;
    x->nw = (m + 63) / 64;
    if (x->nw == 0) x->nw = 1;
    for (int i = 0; i < m; i++) x->glob[i] = idx[ord[i]];
    for (int i = 0; i < m; i++) {
        memset(x->adj[i], 0, sizeof(uint64_t) * x->nw);
        for (int j = 0; j < m; j++)
            if (j != i && col_of(x->glob[i], x->glob[j]) == c) x->adj[i][j >> 6] |= 1ULL << (j & 63);
    }
    x->target = T - 1;
    x->found = x->aborted = 0;
    x->nodes = 0;
    double t0 = now();
    if (m >= x->target) {
        uint64_t P[MW] = {0};
        for (int i = 0; i < m; i++) P[i >> 6] |= 1ULL << (i & 63);
        expand(x, P, 0);
    }
    double sec = now() - t0;
    char wit[1024] = "";
    if (x->found) {
        int g[64], ok = 1, len = 0;
        g[0] = v;
        for (int i = 0; i < x->target; i++) g[i + 1] = x->glob[x->wit[i]];
        for (int i = 0; i < T; i++)
            for (int j = i + 1; j < T; j++)
                if (col_of(g[i], g[j]) != c) ok = 0;
        len += snprintf(wit + len, sizeof wit - len, ",\"witness_ok\":%s,\"witness\":[", ok ? "true" : "false");
        for (int i = 0; i < T; i++) len += snprintf(wit + len, sizeof wit - len, "%s%d", i ? "," : "", g[i]);
        snprintf(wit + len, sizeof wit - len, "]");
        atomic_fetch_add(&n_found, 1);
    }
    if (x->aborted) atomic_fetch_add(&n_timeout, 1);
    pthread_mutex_lock(&out_mx);
    fprintf(out, "{\"v\":%d,\"c\":%d,\"m\":%d,\"result\":\"%s\",\"nodes\":%lld,\"sec\":%.3f%s}\n", v, c, m,
            x->found ? "found" : (x->aborted ? "timeout" : "none"), x->nodes, sec, wit);
    fflush(out);
    pthread_mutex_unlock(&out_mx);
}

static void *worker(void *arg) {
    ctx_t *x = malloc(sizeof(ctx_t));
    (void)arg;
    for (;;) {
        int i = atomic_fetch_add(&next_task, 1);
        if (i >= ntasks) break;
        run_task(x, &tasks[i]);
    }
    free(x);
    return NULL;
}

static int cmp_task(const void *a, const void *b) {   /* largest P first */
    const task_t *p = a, *q = b;
    if (p->m != q->m) return q->m - p->m;
    if (p->v != q->v) return p->v - q->v;
    return p->c - q->c;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s GRAPH t OUT threads [node_cap] [v_lo v_hi]\n", argv[0]);
        return 2;
    }
    T = atoi(argv[2]);
    int threads = atoi(argv[4]);
    node_cap = argc > 5 ? atoll(argv[5]) : 0;
    int vlo = argc > 7 ? atoi(argv[6]) : 0, vhi = argc > 7 ? atoi(argv[7]) : MAXN;
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("graph"); return 2; }
    static char line[MAXN + 4];
    char **rows = malloc(sizeof(char *) * MAXN);
    while (fgets(line, sizeof line, f)) {
        size_t L = strcspn(line, "\r\n");
        if (L == 0) continue;
        line[L] = 0;
        rows[n] = strdup(line);
        if (++n >= MAXN) { fprintf(stderr, "too many rows\n"); return 2; }
    }
    fclose(f);
    A = malloc((size_t)n * n);
    for (int i = 0; i < n; i++) {
        if ((int)strlen(rows[i]) != n) { fprintf(stderr, "row %d has wrong length\n", i); return 2; }
        for (int j = 0; j < n; j++) A[(size_t)i * n + j] = rows[i][j] == '1';
    }
    for (int i = 0; i < n; i++) {
        if (A[(size_t)i * n + i]) { fprintf(stderr, "loop at %d\n", i); return 2; }
        for (int j = 0; j < i; j++)
            if (A[(size_t)i * n + j] != A[(size_t)j * n + i]) { fprintf(stderr, "asymmetric %d %d\n", i, j); return 2; }
    }
    /* tasks already finished (result none/found) in OUT are skipped */
    static unsigned char done[MAXN][2];
    FILE *old = fopen(argv[3], "r");
    if (old) {
        static char buf[4096];
        while (fgets(buf, sizeof buf, old)) {
            int v, c;
            if (sscanf(buf, "{\"v\":%d,\"c\":%d", &v, &c) == 2 && !strstr(buf, "\"timeout\"") && v >= 0 && v < MAXN)
                done[v][c & 1] = 1;
        }
        fclose(old);
    }
    tasks = malloc(sizeof(task_t) * 2 * n);
    for (int v = 0; v < n; v++) {
        if (v < vlo || v >= vhi) continue;
        for (int c = 0; c < 2; c++) {
            if (done[v][c]) continue;
            int m = 0;
            for (int w = v + 1; w < n; w++) m += A[(size_t)v * n + w] == c;
            if (m > MAXM) { fprintf(stderr, "P too large (%d) at v=%d\n", m, v); return 2; }
            tasks[ntasks++] = (task_t){v, c, m};
        }
    }
    qsort(tasks, ntasks, sizeof(task_t), cmp_task);
    out = fopen(argv[3], "a");
    if (!out) { perror("out"); return 2; }
    fprintf(stderr, "n=%d t=%d tasks=%d threads=%d cap=%lld\n", n, T, ntasks, threads, node_cap);
    pthread_t th[256];
    for (int i = 0; i < threads; i++) pthread_create(&th[i], NULL, worker, NULL);
    for (int i = 0; i < threads; i++) pthread_join(th[i], NULL);
    fclose(out);
    fprintf(stderr, "finished: found=%d timeout=%d\n", atomic_load(&n_found), atomic_load(&n_timeout));
    return 0;
}
