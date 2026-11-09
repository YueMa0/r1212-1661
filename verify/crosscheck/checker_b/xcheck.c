/* xcheck -- checker B: exact checker for colourings of clone type over M(797).
 * usage: xcheck GRAPH TYPES [TIGHT_OUT]
 * TYPES file: first token line "SIGMA k g1 .. gk" (M indices), then one line per vertex of
 * the graph, in order: "V m" (vertex is M-point m of V0) or "T g" (typed point, g an M index
 * in Sigma) or "T R" / "T B".  types_from_json.py writes it from graph/r1212_1660.json.
 * TIGHT_OUT (optional) receives the type sets with slack 0.
 * Checks: (1) V0 = V \ Sigma, each M point of V0 exactly once; (2) V0-V0 colours equal M;
 * (3) T-V0 colours follow the types; (4) every (not only maximal) monochromatic clique K of
 * T satisfies (i) |K| <= 11 if it contains an opposite constant, (ii) |K| + e_c(D(K)) <= 11
 * otherwise. e_c is computed by mlib.h (upper bound 10 - omega^M_c(D) from "M has no
 * monochromatic K11", then exhaustive search below it). (1)-(4) together are equivalent to
 * "no monochromatic K12"; the argument is in verify/crosscheck/README.md. */
#include "mlib.h"

#define MAXT 512
#define TW (MAXT / 64)
typedef unsigned __int128 u128;

static int n, ns, sig[128], sigpos[NM];
static uint8_t inS[NM];
static uint8_t *H;
static int isT[1 << 13], mpt[1 << 13], tty[1 << 13];   /* tty: sigma index, -1 R, -2 B */
static int Tlist[MAXT], nT;
static uint64_t Tadj[2][MAXT][TW];

/* hash map dmask -> max clique size (per colour) */
typedef struct { u128 key; int used, maxsz, rep[16]; } Ent;
static Ent *tab[2]; static size_t tcap = 1 << 22, tcnt[2];
static long long ncl[2], nopp_bad = 0, opp_max[2];

static size_t hsh(u128 k) { uint64_t a = (uint64_t)k, b = (uint64_t)(k >> 64);
    uint64_t h = a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL) * 0xBF58476D1CE4E5B9ULL;
    return (size_t)(h ^ (h >> 29)); }

static void record(int c, u128 dm, int sz, const int *K) {
    size_t i = hsh(dm) & (tcap - 1);
    while (tab[c][i].used && tab[c][i].key != dm) i = (i + 1) & (tcap - 1);
    Ent *e = &tab[c][i];
    if (!e->used) { e->used = 1; e->key = dm; e->maxsz = 0; tcnt[c]++;
        if (tcnt[c] > tcap / 2) { fprintf(stderr, "hash full\n"); exit(2); } }
    if (sz > e->maxsz) { e->maxsz = sz; for (int j = 0; j < sz && j < 16; j++) e->rep[j] = K[j]; }
}

static int Kst[64];
static void enum_cl(int c, const uint64_t *P, int sz, u128 dm, int opp) {
    uint64_t Q[TW]; memcpy(Q, P, sizeof Q);
    for (int w = 0; w < TW; w++) while (Q[w]) {
        int i = w * 64 + __builtin_ctzll(Q[w]); Q[w] &= Q[w] - 1;
        int t = tty[Tlist[i]];
        u128 d2 = dm; int o2 = opp;
        if (t >= 0) d2 |= (u128)1 << t;
        else if ((c == 1 && t == -2) || (c == 0 && t == -1)) o2 = 1;
        Kst[sz] = i;
        ncl[c]++;
        if (o2) { if (sz + 1 > opp_max[c]) opp_max[c] = sz + 1;
                  if (sz + 1 > 11) nopp_bad++; }
        else record(c, d2, sz + 1, Kst);
        uint64_t NP[TW]; int any = 0;
        for (int j = 0; j < TW; j++) { NP[j] = (j < w ? 0 : (j == w ? Q[w] : Q[j])) & Tadj[c][i][j]; any |= NP[j] != 0; }
        if (any) enum_cl(c, NP, sz + 1, d2, o2);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: xcheck GRAPH TYPES [TIGHT_OUT]\n"); return 1; }
    build_M();
    /* read graph */
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("graph"); return 1; }
    static char line[1 << 14]; int r = 0;
    while (fgets(line, sizeof line, f)) {
        int L = strlen(line); if (L && line[L - 1] == '\n') line[--L] = 0;
        if (r == 0) { n = L; H = malloc((size_t)n * n); }
        if (L != n) { printf("FAIL row %d length %d != %d\n", r, L, n); return 1; }
        for (int v = 0; v < n; v++) {
            if (line[v] != '0' && line[v] != '1') { printf("FAIL bad char\n"); return 1; }
            H[(size_t)r * n + v] = line[v] == '1';
        }
        r++;
    }
    fclose(f);
    if (r != n) { printf("FAIL %d rows for %d columns\n", r, n); return 1; }
    long long asym = 0;
    for (int u = 0; u < n; u++) { if (H[(size_t)u * n + u]) asym++;
        for (int v = u + 1; v < n; v++) if (H[(size_t)u * n + v] != H[(size_t)v * n + u]) asym++; }
    if (asym) { printf("FAIL asymmetric or nonzero diagonal (%lld)\n", asym); return 1; }
    /* read types */
    f = fopen(argv[2], "r"); if (!f) { perror("types"); return 1; }
    char tok[64];
    if (fscanf(f, "%63s %d", tok, &ns) != 2 || strcmp(tok, "SIGMA") || ns > 127) { printf("FAIL types header\n"); return 1; }
    memset(sigpos, -1, sizeof sigpos);
    for (int i = 0; i < ns; i++) { if (fscanf(f, "%d", &sig[i]) != 1 || sig[i] < 0 || sig[i] >= NM || inS[sig[i]]) { printf("FAIL sigma\n"); return 1; }
        inS[sig[i]] = 1; sigpos[sig[i]] = i; }
    static int seen[NM];
    for (int v = 0; v < n; v++) {
        char a[8], b[16];
        if (fscanf(f, "%7s %15s", a, b) != 2) { printf("FAIL types: missing vertex %d\n", v); return 1; }
        if (!strcmp(a, "V")) { int m = atoi(b); if (m < 0 || m >= NM || inS[m] || seen[m]) { printf("FAIL V0 point %d at %d\n", m, v); return 1; }
            seen[m] = 1; isT[v] = 0; mpt[v] = m; }
        else if (!strcmp(a, "T")) { isT[v] = 1;
            if (!strcmp(b, "R")) tty[v] = -1; else if (!strcmp(b, "B")) tty[v] = -2;
            else { int g = atoi(b); if (g < 0 || g >= NM || !inS[g]) { printf("FAIL type %s at %d\n", b, v); return 1; } tty[v] = sigpos[g]; }
            if (nT >= MAXT) { printf("FAIL too many T\n"); return 1; }
            Tlist[nT++] = v; }
        else { printf("FAIL types line %d\n", v); return 1; }
    }
    fclose(f);
    int nv0 = 0; for (int m = 0; m < NM; m++) if (!inS[m]) { if (!seen[m]) { printf("FAIL V0 point %d missing\n", m); return 1; } nv0++; }
    printf("n=%d |V0|=%d |Sigma|=%d |T|=%d  |T|-|Sigma|=%d\n", n, nv0, ns, nT, nT - ns);
    /* (2),(3) */
    long long bad2 = 0, bad3 = 0;
    for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) {
        if (u == v || isT[v]) continue;
        int h = H[(size_t)u * n + v];
        if (!isT[u]) { if (h != Mc[mpt[u]][mpt[v]]) bad2++; }
        else { int t = tty[u]; int want = t == -1 ? 1 : t == -2 ? 0 : Mc[sig[t]][mpt[v]]; if (h != want) bad3++; }
    }
    printf("V0-V0 mismatches %lld, T-V0 type mismatches %lld\n", bad2, bad3);
    /* (4) */
    for (int c = 0; c < 2; c++) for (int i = 0; i < nT; i++) for (int j = 0; j < nT; j++)
        if (i != j && H[(size_t)Tlist[i] * n + Tlist[j]] == c) Tadj[c][i][j >> 6] |= 1ULL << (j & 63);
    long long viol = 0, tight = 0;
    FILE *to = argc > 3 ? fopen(argv[3], "w") : NULL;
    for (int c = 1; c >= 0; c--) {
        tab[c] = calloc(tcap, sizeof(Ent));
        uint64_t P[TW] = {0}; for (int i = 0; i < nT; i++) P[i >> 6] |= 1ULL << (i & 63);
        enum_cl(c, P, 0, 0, 0);
        int maxsz_any = 0;
        for (size_t s = 0; s < tcap; s++) {
            Ent *e = &tab[c][s]; if (!e->used) continue;
            if (e->maxsz > maxsz_any) maxsz_any = e->maxsz;
            int D[128], d = 0;
            for (int i = 0; i < ns; i++) if ((e->key >> i) & 1) D[d++] = sig[i];
            int n0, ub;
            int ub0 = 10 - (d ? omega_small(D, d, c) : 0);
            if (e->maxsz + ub0 <= 10) continue;        /* slack >= 1 already from the bound */
            int ev = ec_value(c, D, d, inS, &n0, &ub, NULL, 0);
            if (ev < 0) { printf("FAIL oracle aborted\n"); return 1; }
            int sl = 11 - ev - e->maxsz;
            if (sl < 0) { viol++; if (viol <= 40) { printf("VIOLATION %s |K|=%d e=%d |N0|=%d D={", c ? "red" : "blue", e->maxsz, ev, n0);
                for (int i = 0; i < d; i++) printf(i ? ",%d" : "%d", D[i]); printf("} K="); for (int j = 0; j < e->maxsz && j < 16; j++) printf(" %d", Tlist[e->rep[j]]); printf("\n"); } }
            if (sl == 0) { tight++;
                if (to) { fprintf(to, "%s\t%d\t%d\t", c ? "red" : "blue", e->maxsz, ev);
                    for (int i = 0; i < d; i++) fprintf(to, i ? ",%d" : "%d", D[i]); fprintf(to, "\t");
                    for (int j = 0; j < e->maxsz && j < 16; j++) fprintf(to, j ? ",%d" : "%d", Tlist[e->rep[j]]); fprintf(to, "\n"); } }
        }
        printf("%s: cliques in T %lld, distinct type sets %zu, max |K| %d, max |K| with opposite constant %lld\n",
               c ? "red" : "blue", ncl[c], tcnt[c], maxsz_any, opp_max[c]);
        free(tab[c]);
    }
    if (to) fclose(to);
    printf("opposite-constant violations %lld, capacity violations %lld, tight type sets %lld\n", nopp_bad, viol, tight);
    int ok = !bad2 && !bad3 && !nopp_bad && !viol;
    printf("%s\n", ok ? "PASS" : "FAIL");
    return !ok;
}
