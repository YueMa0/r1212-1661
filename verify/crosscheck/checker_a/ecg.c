/* e_c(D) oracle of checker A, for a target set Sigma_V of at most 32 vertices of M(797).
   e_c(D) = largest colour-c clique of M inside N0_c(D) = {v in V0 : gv has colour c for all g in D},
   where V0 = M(797) minus Sigma_V.  Built as a shared library and loaded by exact_check_general.py
   through ctypes:  cc -O3 -shared -fPIC -o libecg.so verify/crosscheck/checker_a/ecg.c
   Exactness: a value e < ub is proved by exhaustive branch and bound; the search stops early only
   when it finds a clique of size ub, where ub = min(10 - omega^M_c(D), e_c(D minus one point) if
   already known).  The first term uses omega(M(797)) <= 10 (Mathon). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define P797 797
#define NV 1596
#define NW 25          /* words for 1596 bits */
#define MAXS 32
static int NS = 0;

static uint64_t ADJ[2][NV][NW];   /* ADJ[c][v]: colour-c neighbours in M */
static uint64_t V0MASK[NW];
static int SIG[MAXS];
static uint32_t SADJ[2][MAXS];    /* colour-c adjacency inside Sigma in M */
static int HBITS = 22;
static uint64_t *HK; static int8_t *HV;   /* hash cache: key = (D << 1 | c) + 1 */
static int inited = 0;
static int8_t hget(int c, uint32_t D) {
    uint64_t key = (((uint64_t)D << 1) | (uint64_t)c) + 1, i = (key * 0x9E3779B97F4A7C15ULL) >> (64 - HBITS);
    while (HK[i]) { if (HK[i] == key) return HV[i]; i = (i + 1) & ((1ULL << HBITS) - 1); }
    return -1;
}
static void hput(int c, uint32_t D, int8_t v) {
    uint64_t key = (((uint64_t)D << 1) | (uint64_t)c) + 1, i = (key * 0x9E3779B97F4A7C15ULL) >> (64 - HBITS);
    while (HK[i] && HK[i] != key) i = (i + 1) & ((1ULL << HBITS) - 1);
    HK[i] = key; HV[i] = v;
}

static int color_M(int u, int v) {
    if (u == v) return -1;
    if (u > v) { int t = u; u = v; v = t; }
    if (v == 1594) return u < P797 ? 1 : 0;
    if (v == 1595) return (u >= P797 && u < 2 * P797) ? 1 : 0;
    if (u == 1594) return 0;   /* u=1594, v=1595 */
    static int sq[P797]; static int sqi = 0;
    if (!sqi) { for (int i = 1; i < P797; i++) sq[(i * i) % P797] = 1; sqi = 1; }
    int ua = u < P797, va = v < P797;
    int x = ua ? u : u - P797, y = va ? v : v - P797;
    int d = ((x - y) % P797 + P797) % P797;
    if (ua == va) return (d != 0 && sq[d]) ? 1 : 0;
    return (d != 0 && !sq[d]) ? 1 : 0;
}

int ec_init(int ns, const int *sig) {
    if (inited) return 0;
    NS = ns; for (int j = 0; j < ns; j++) SIG[j] = sig[j];
    memset(ADJ, 0, sizeof ADJ);
    for (int u = 0; u < NV; u++)
        for (int v = 0; v < NV; v++) if (u != v) {
            int c = color_M(u, v);
            ADJ[c][u][v >> 6] |= 1ULL << (v & 63);
        }
    memset(V0MASK, 0, sizeof V0MASK);
    for (int v = 0; v < NV; v++) V0MASK[v >> 6] |= 1ULL << (v & 63);
    for (int j = 0; j < NS; j++) V0MASK[SIG[j] >> 6] &= ~(1ULL << (SIG[j] & 63));
    for (int c = 0; c < 2; c++)
        for (int a = 0; a < NS; a++) {
            SADJ[c][a] = 0;
            for (int b = 0; b < NS; b++)
                if (a != b && color_M(SIG[a], SIG[b]) == c) SADJ[c][a] |= 1u << b;
        }
    if (ns + 3 > HBITS) HBITS = ns + 3;      /* room for both colours of every subset, load <= 1/4 */
    HK = calloc((size_t)1 << HBITS, 8); HV = calloc((size_t)1 << HBITS, 1);
    inited = 1;
    return 0;
}

int ec_color_M(int u, int v) { return color_M(u, v); }

/* omega of colour c inside D (a subset of Sigma) in M */
static int om_rec(int c, uint32_t P, int sz) {
    if (!P) return sz;
    int best = sz;
    while (P) {
        if (sz + __builtin_popcount(P) <= best) break;
        int v = __builtin_ctz(P);
        P &= P - 1;
        int r = om_rec(c, P & SADJ[c][v], sz + 1);
        if (r > best) best = r;
    }
    return best;
}
int omega_sig(int c, uint32_t D) { return om_rec(c, D, 0); }

/* ---------- max clique on a compact local graph (BBMC style) ---------- */
typedef struct {
    int m, W;
    uint64_t *adj;          /* m * W */
    int best, ub;
    int cur[64], wit[64];
    long long nodes;
} MC;

static void mc_expand(MC *S, uint64_t *P, int sz, int depth) {
    int W = S->W, m = S->m;
    int order[m], colv[m];
    uint64_t U[W], Q[W];
    memcpy(U, P, W * 8);
    int cnt = 0, k = 0;
    S->nodes++;
    int any = 1;
    while (any) {
        any = 0;
        for (int w = 0; w < W; w++) if (U[w]) { any = 1; break; }
        if (!any) break;
        k++;
        memcpy(Q, U, W * 8);
        for (int w = 0; w < W; w++) {
            while (Q[w]) {
                int v = w * 64 + __builtin_ctzll(Q[w]);
                Q[w] &= Q[w] - 1;
                U[w] &= ~(1ULL << (v & 63));
                const uint64_t *av = S->adj + (size_t)v * W;
                for (int x = w; x < W; x++) Q[x] &= ~av[x];
                order[cnt] = v; colv[cnt] = k; cnt++;
            }
        }
    }
    uint64_t NP[W];
    for (int i = cnt - 1; i >= 0; i--) {
        if (sz + colv[i] <= S->best) return;
        int v = order[i];
        const uint64_t *av = S->adj + (size_t)v * W;
        int nz = 0;
        for (int w = 0; w < W; w++) { NP[w] = P[w] & av[w]; nz |= NP[w] != 0; }
        S->cur[sz] = v;
        if (!nz) {
            if (sz + 1 > S->best) {
                S->best = sz + 1;
                memcpy(S->wit, S->cur, sizeof(int) * (sz + 1));
            }
        } else {
            mc_expand(S, NP, sz + 1, depth + 1);
        }
        if (S->best >= S->ub) return;
        P[v >> 6] &= ~(1ULL << (v & 63));
    }
}

/* max colour-c clique inside the candidate list cand[0..m-1] of M, stop at ub.
   wit (if non-NULL) receives the clique (global vertex ids); returns its size. */
static int maxclique_M(int c, const int *cand, int m, int ub, int *wit, long long *nodes) {
    if (m == 0) return 0;
    MC S;
    S.m = m; S.W = (m + 63) / 64;
    S.adj = calloc((size_t)m * S.W, 8);
    for (int i = 0; i < m; i++)
        for (int j = 0; j < m; j++)
            if (i != j && (ADJ[c][cand[i]][cand[j] >> 6] >> (cand[j] & 63) & 1))
                S.adj[(size_t)i * S.W + (j >> 6)] |= 1ULL << (j & 63);
    S.best = 0; S.ub = ub; S.nodes = 0;
    uint64_t P[S.W];
    memset(P, 0, sizeof P);
    for (int i = 0; i < m; i++) P[i >> 6] |= 1ULL << (i & 63);
    mc_expand(&S, P, 0, 0);
    if (wit) for (int i = 0; i < S.best; i++) wit[i] = cand[S.wit[i]];
    if (nodes) *nodes = S.nodes;
    free(S.adj);
    return S.best;
}

int ec_cand(int c, uint32_t D, int *cand) {
    uint64_t P[NW];
    memcpy(P, V0MASK, sizeof P);
    for (int j = 0; j < NS; j++) if (D >> j & 1)
        for (int w = 0; w < NW; w++) P[w] &= ADJ[c][SIG[j]][w];
    int m = 0;
    for (int w = 0; w < NW; w++) {
        uint64_t x = P[w];
        while (x) { cand[m++] = w * 64 + __builtin_ctzll(x); x &= x - 1; }
    }
    return m;
}

int ec_bound(int c, uint32_t D) { return 10 - omega_sig(c, D); }

/* compute (no cache read for D itself); ub from the bound and known subsets */
int ec_compute(int c, uint32_t D, int *wit, long long *nodes, int *msize) {
    int cand[NV];
    int m = ec_cand(c, D, cand);
    if (msize) *msize = m;
    int ub = ec_bound(c, D);
    for (int j = 0; j < NS; j++) if (D >> j & 1) {
        int s = hget(c, D & ~(1u << j));
        if (s >= 0 && s < ub) ub = s;
    }
    if (ub > m) ub = m;
    return maxclique_M(c, cand, m, ub, wit, nodes);
}

/* same, but with an explicit ub (used to re-prove without the theorem cut) */
int ec_compute_ub(int c, uint32_t D, int ub, int *wit, long long *nodes) {
    int cand[NV];
    int m = ec_cand(c, D, cand);
    return maxclique_M(c, cand, m, ub, wit, nodes);
}

int ec_get(int c, uint32_t D) {
    int8_t t = hget(c, D);
    if (t >= 0) return t;
    int r = ec_compute(c, D, NULL, NULL, NULL);
    hput(c, D, (int8_t)r);
    return r;
}

