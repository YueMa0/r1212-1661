/* mlib.h -- checker B: the Mathon-Shearer colouring M(797) built from its definition,
 * and a bitset branch-and-bound maximum clique routine (greedy colouring bound).
 * Written independently of checker A; header-only. */
#ifndef MLIB_H
#define MLIB_H
#include <alloca.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define P797 797
#define NM 1596
#define WM ((NM + 63) / 64)

static uint8_t Mc[NM][NM];          /* 1 = red, 0 = blue, diagonal 0 */
static uint64_t Mbits[2][NM][WM];   /* Mbits[c][v] = c-neighbours of v (c: 1 red, 0 blue) */

static void build_M(void) {
    static int sq[P797];
    memset(sq, 0, sizeof sq);
    for (int x = 1; x < P797; x++) sq[(x * x) % P797] = 1;
    for (int u = 0; u < NM; u++)
        for (int v = 0; v < NM; v++) {
            int r = 0;
            if (u == v) r = 0;
            else if (u < 1594 && v < 1594) {
                int uA = u < P797, vA = v < P797;
                int xu = uA ? u : u - P797, xv = vA ? v : v - P797;
                int d = ((xu - xv) % P797 + P797) % P797;
                if (uA == vA) r = (d != 0 && sq[d]);
                else r = (d != 0 && !sq[d]);
            } else {
                int s = u, t = v;
                if (s < t) { int k = s; s = t; t = k; }   /* s is a or b */
                if (s == 1594 && t < P797) r = 1;
                else if (s == 1595 && t >= P797 && t < 1594) r = 1;
                else r = 0;
            }
            Mc[u][v] = (uint8_t)r;
        }
    memset(Mbits, 0, sizeof Mbits);
    for (int u = 0; u < NM; u++)
        for (int v = 0; v < NM; v++)
            if (u != v) Mbits[Mc[u][v]][u][v >> 6] |= 1ULL << (v & 63);
}

/* ---------- compact graph + max clique ---------- */
typedef struct {
    int n, W;
    uint64_t *adj;      /* n * W */
    int best, stop;
    int cur[64], wit[64];
    long long nodes;
    long long node_cap; /* 0 = unlimited */
    int aborted;
} MC;

static inline int bs_empty(const uint64_t *a, int W) {
    for (int i = 0; i < W; i++) if (a[i]) return 0;
    return 1;
}

static void mc_expand(MC *x, uint64_t *P, int depth) {
    int W = x->W, n = x->n;
    int *order = (int *)alloca(sizeof(int) * n);
    int *col = (int *)alloca(sizeof(int) * n);
    uint64_t *Q = (uint64_t *)alloca(8 * W), *U = (uint64_t *)alloca(8 * W);
    uint64_t *NP = (uint64_t *)alloca(8 * W);
    x->nodes++;
    if (x->node_cap && x->nodes > x->node_cap) { x->aborted = 1; return; }
    memcpy(Q, P, 8 * W);
    int cnt = 0, k = 0;
    while (!bs_empty(Q, W)) {
        k++;
        memcpy(U, Q, 8 * W);
        for (int w = 0; w < W; w++) {
            while (U[w]) {
                int v = w * 64 + __builtin_ctzll(U[w]);
                U[w] &= U[w] - 1;
                Q[w] &= ~(1ULL << (v & 63));
                const uint64_t *a = x->adj + (size_t)v * W;
                for (int j = w; j < W; j++) U[j] &= ~a[j];
                order[cnt] = v; col[cnt] = k; cnt++;
            }
        }
    }
    for (int i = cnt - 1; i >= 0; i--) {
        if (depth + col[i] <= x->best) return;
        int v = order[i];
        x->cur[depth] = v;
        const uint64_t *a = x->adj + (size_t)v * W;
        int any = 0;
        for (int w = 0; w < W; w++) { NP[w] = P[w] & a[w]; any |= NP[w] != 0; }
        if (!any) {
            if (depth + 1 > x->best) {
                x->best = depth + 1;
                memcpy(x->wit, x->cur, sizeof(int) * (depth + 1));
                if (x->best >= x->stop) return;
            }
        } else {
            mc_expand(x, NP, depth + 1);
            if (x->best >= x->stop || x->aborted) return;
        }
        P[v >> 6] &= ~(1ULL << (v & 63));
    }
}

/* Maximum c-clique of M induced on vertex list S[0..k-1].
 * Stops as soon as a clique of size >= stop is found (stop <= 0: no early stop).
 * Returns the size found; *exact = 1 if the value is exact (search completed or reached stop).
 * If wit != NULL, writes witness M-indices. node_cap bounds the search (0 = none). */
static int mc_on_list(const int *S, int k, int c, int stop, int *wit, long long node_cap, int *exact) {
    if (k == 0) { if (exact) *exact = 1; return 0; }
    /* order by c-degree inside S, descending */
    int *ord = (int *)malloc(sizeof(int) * k), *deg = (int *)malloc(sizeof(int) * k);
    for (int i = 0; i < k; i++) {
        int d = 0;
        for (int j = 0; j < k; j++) if (j != i && Mc[S[i]][S[j]] == c) d++;
        deg[i] = d; ord[i] = i;
    }
    for (int i = 1; i < k; i++) {          /* insertion sort, descending degree */
        int t = ord[i], j = i - 1;
        while (j >= 0 && deg[ord[j]] < deg[t]) { ord[j + 1] = ord[j]; j--; }
        ord[j + 1] = t;
    }
    MC x; memset(&x, 0, sizeof x);
    x.n = k; x.W = (k + 63) / 64;
    x.adj = (uint64_t *)calloc((size_t)k * x.W, 8);
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            if (i != j && Mc[S[ord[i]]][S[ord[j]]] == c)
                x.adj[(size_t)i * x.W + (j >> 6)] |= 1ULL << (j & 63);
    x.best = 0; x.stop = stop > 0 ? stop : 1 << 30; x.node_cap = node_cap;
    uint64_t *P = (uint64_t *)calloc(x.W, 8);
    for (int i = 0; i < k; i++) P[i >> 6] |= 1ULL << (i & 63);
    x.best = 1; x.wit[0] = 0; x.cur[0] = 0;      /* any single vertex */
    if (x.best < x.stop) mc_expand(&x, P, 0);
    if (wit) for (int i = 0; i < x.best; i++) wit[i] = S[ord[x.wit[i]]];
    if (exact) *exact = !x.aborted;
    int r = x.best;
    free(P); free(x.adj); free(ord); free(deg);
    return r;
}

/* omega^M_c(D) for a small list D */
static int omega_small(const int *D, int d, int c) {
    int ex;
    return mc_on_list(D, d, c, 0, NULL, 0, &ex);
}

/* e_c(D) w.r.t. Sigma (inSigma[v] = 1 for target points). Uses the valid upper bound
 * e_c(D) <= 10 - omega^M_c(D) (M has no monochromatic K11), stops when it is reached,
 * otherwise searches exhaustively. *n0 gets |N0_c(D)|. Returns -1 if node cap hit. */
static int ec_value(int c, const int *D, int d, const uint8_t *inSigma, int *n0, int *ub_out,
                    int *wit, long long node_cap) {
    int *S = (int *)malloc(sizeof(int) * NM), k = 0;
    for (int v = 0; v < NM; v++) {
        if (inSigma[v]) continue;
        int ok = 1;
        for (int i = 0; i < d && ok; i++) if (Mc[D[i]][v] != c) ok = 0;
        if (ok) S[k++] = v;
    }
    int ub = 10 - (d ? omega_small(D, d, c) : 0);
    if (n0) *n0 = k;
    if (ub_out) *ub_out = ub;
    int ex = 1, e;
    if (ub <= 0) {
        if (k > 0) { fprintf(stderr, "FATAL: D contains a K10 but N0 nonempty\n"); exit(3); }
        e = 0;
    } else e = mc_on_list(S, k, c, ub, wit, node_cap, &ex);
    free(S);
    if (!ex) return -1;
    return e;
}
#endif
