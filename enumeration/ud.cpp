// Graphes sans sous-graphe interdit proches du maximum d'arêtes, pour le problème des distances unité d'Erdős :
// tous les graphes à N sommets et M arêtes sans aucun des 74 graphes interdits de Globus–Parshall (forbidden.txt),
// et, avec l'option tu, sans motif « totalement infidèle » (sous-graphe qui force deux sommets non adjacents à être
// à distance 1 : impossible dans le graphe complet des distances unité d'un ensemble de points, propriété qui passe
// aux sous-graphes induits, donc appliquée à tous les niveaux).
// Construction sommet par sommet (Schade ; Alexeev–Mixon–Parshall, arXiv:2412.11914) : le sommet ajouté est de
// degré minimal dans le nouveau graphe, et chaque graphe n'est gardé que depuis son parent canonique (augmentation
// canonique de McKay, nauty), donc produit une seule fois, sans stocker les niveaux.
// Usage : ud N M [tu] [stats] [res/mod à profondeur P : part R MOD P]
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <set>
#include <string>
#include <vector>
#define MAXN 32
#include "nauty.h"
typedef uint32_t u32;

static const int UBAR[] = {0, 0, 1, 3, 5, 7, 9, 12, 14, 18, 20, 23, 27, 30, 33, 37, 41, 43, 46, 50, 54, 57, 62, 66};
static int NT, MT; static bool TU = false, STATS = false;
static int RES = -1, MOD = 0, PROF = 0;

struct Motif {             // motif à plonger dans H (monomorphisme), sommets-clés d'abord
    int k, ncle, nS; u32 adj[10]; int ordre[10]; int deg[10];
    int na, nb;            // contrainte de non-arête (ou -1)
    int ycle;              // position du sommet y parmi les clés (implication), ou -1
    bool base;             // motif de K4 ou K2,3 : traité d'avance, pour filtrer les voisinages candidats
};
static std::vector<Motif> motifs;

static bool BASE = false;
static void ajoute_motif(int k, const u32 *adjF, int p, int na, int nb, int y) {
    // Q = F - p ; S = N(p) ; clés = S (puis y si implication)
    Motif m; memset(&m, 0, sizeof m);
    int idx[10], inv[10], t = 0;
    for (int i = 0; i < k; i++) if (i != p) { idx[t] = i; inv[i] = t++; }
    m.k = k - 1;
    for (int i = 0; i < m.k; i++) for (int j = 0; j < m.k; j++) if (adjF[idx[i]] >> idx[j] & 1) m.adj[i] |= 1u << j;
    for (int i = 0; i < m.k; i++) m.deg[i] = __builtin_popcount(m.adj[i]);
    std::vector<int> cles;
    for (int i = 0; i < m.k; i++) if (adjF[p] >> idx[i] & 1) cles.push_back(i);
    m.nS = cles.size();
    m.ycle = -1;
    if (y >= 0) { m.ycle = cles.size(); cles.push_back(inv[y]); }
    m.ncle = cles.size();
    m.na = na >= 0 ? inv[na] : -1; m.nb = nb >= 0 ? inv[nb] : -1;
    u32 fait = 0; int n = 0;
    for (int c : cles) { m.ordre[n++] = c; fait |= 1u << c; }
    while (n < m.k) {       // ensuite : le sommet le plus lié à ceux déjà placés
        int best = -1, bs = -1;
        for (int i = 0; i < m.k; i++) if (!(fait >> i & 1)) { int s = __builtin_popcount(m.adj[i] & fait) * 16 + m.deg[i]; if (s > bs) { bs = s; best = i; } }
        m.ordre[n++] = best; fait |= 1u << best;
    }
    m.base = BASE;
    motifs.push_back(m);
}

// --- graphe courant ---
static u32 adjH[MAXN]; static int degH[MAXN];
static int nH;

struct Mauvais { std::vector<u32> purs; std::vector<std::pair<u32, int>> impl; std::vector<u32> parMax[MAXN]; };

static const Motif *PM; static int img[10]; static u32 pris;
static bool existe(int i) {
    const Motif &m = *PM;
    if (i == m.k) return true;
    int q = m.ordre[i];
    u32 cand = ~pris & ((nH == 32) ? ~0u : ((1u << nH) - 1));
    for (int r = 0; r < i; r++) { int o = m.ordre[r]; if (m.adj[q] >> o & 1) cand &= adjH[img[o]]; }
    if (q == m.na && img[m.nb] >= 0) cand &= ~adjH[img[m.nb]];
    if (q == m.nb && img[m.na] >= 0) cand &= ~adjH[img[m.na]];
    for (; cand; cand &= cand - 1) {
        int v = __builtin_ctz(cand);
        if (degH[v] < m.deg[q]) continue;
        img[q] = v; pris |= 1u << v;
        bool ok = existe(i + 1);
        pris &= ~(1u << v); img[q] = -1;
        if (ok) return true;
    }
    return false;
}
static std::vector<int> ordreMotifs;
static Mauvais *OUT; static int DMAX;
static bool TEST = false, TROUVE = false; static u32 NCAND, TTROUVE;   // mode « tester un voisinage candidat »
static std::vector<u32> parSommet[MAXN];      // ensembles interdits purs connus, rangés sous chacun de leurs sommets
static inline bool contient_interdit(u32 T, int v) {   // T contient-il un ensemble interdit passant par v ?
    for (u32 U : parSommet[v]) if ((U & T) == U) return true;
    return false;
}
static void note_pur(u32 T) {
    OUT->purs.push_back(T);
    for (u32 x = T; x; x &= x - 1) parSommet[__builtin_ctz(x)].push_back(T);
}
static void cles(int i, u32 T) {
    const Motif &m = *PM;
    if (i == m.ncle) {
        int w = m.ycle >= 0 ? img[m.ordre[m.ycle]] : -1;
        if (TEST) { if (existe(i)) { TROUVE = true; TTROUVE = w < 0 ? T : 0; } return; }
        // l'existence dépend de l'affectation des clés, pas seulement de l'ensemble image
        if (w >= 0) { for (auto &pr : OUT->impl) if (pr.first == T && pr.second == w) return; }
        if (existe(i)) { if (w < 0) note_pur(T); else OUT->impl.push_back({T, w}); }
        return;
    }
    int q = m.ordre[i];
    bool estS = i < m.nS;
    u32 cand = ~pris & ((nH == 32) ? ~0u : ((1u << nH) - 1));
    if (TEST) cand &= estS ? NCAND : ~NCAND;      // S dans le voisinage candidat ; y hors du voisinage
    for (int r = 0; r < i; r++) { int o = m.ordre[r]; if (m.adj[q] >> o & 1) cand &= adjH[img[o]]; }
    if (q == m.na && img[m.nb] >= 0) cand &= ~adjH[img[m.nb]];
    if (q == m.nb && img[m.na] >= 0) cand &= ~adjH[img[m.na]];
    for (; cand; cand &= cand - 1) {
        if (TROUVE) return;
        int v = __builtin_ctz(cand);
        if (degH[v] < m.deg[q]) continue;
        u32 T2 = T;
        if (estS) { T2 |= 1u << v; if (!TEST && contient_interdit(T2, v)) continue; }   // voisinage déjà exclu
        img[q] = v; pris |= 1u << v;
        cles(i + 1, T2);
        pris &= ~(1u << v); img[q] = -1;
    }
}
static void mauvais_voisinages(Mauvais &out, int dmax) {
    out.purs.clear(); out.impl.clear();
    OUT = &out; DMAX = dmax;
    for (int v = 0; v < nH; v++) parSommet[v].clear();
    for (int im : ordreMotifs) {            // petits S d'abord : leurs ensembles interdits élaguent les suivants
        const Motif &m = motifs[im];
        if (!m.base || m.nS > dmax || m.k > nH) continue;
        PM = &m; pris = 0;
        for (int i = 0; i < 10; i++) img[i] = -1;
        cles(0, 0);
    }
    std::sort(out.purs.begin(), out.purs.end(), [](u32 a, u32 b) { int x = __builtin_popcount(a), y = __builtin_popcount(b); return x != y ? x < y : a < b; });
    out.purs.erase(std::unique(out.purs.begin(), out.purs.end()), out.purs.end());
    std::vector<u32> mini;
    for (u32 T : out.purs) { bool dom = false; for (u32 U : mini) if ((U & T) == U) { dom = true; break; } if (!dom) mini.push_back(T); }
    out.purs.swap(mini);
    for (u32 T : out.purs) out.parMax[31 - __builtin_clz(T)].push_back(T);   // rangés sous leur plus grand sommet
}

// Le voisinage candidat N (sans ensemble interdit de base) crée-t-il un graphe interdit ou un motif infidèle ?
// Si oui et que la cause est un ensemble pur T ⊆ N, T est renvoyé pour élaguer les candidats suivants.
static bool candidat_interdit(u32 N, u32 &Tpur) {
    int d = __builtin_popcount(N);
    TEST = true; NCAND = N; TROUVE = false;
    for (int im : ordreMotifs) {
        const Motif &m = motifs[im];
        if (m.base || m.nS > d || m.k > nH) continue;
        PM = &m; pris = 0;
        for (int i = 0; i < 10; i++) img[i] = -1;
        cles(0, 0);
        if (TROUVE) break;
    }
    TEST = false;
    Tpur = TROUVE ? TTROUVE : 0;
    return TROUVE;
}

// --- accessibilité : (n, m, δ) peut-il mener à (NT, MT) en ajoutant chaque fois un sommet de degré minimal ? ---
static signed char acc[MAXN][128][16];
static bool accessible(int n, int m, int dl) {
    if (m > 127 || dl > 15) return false;
    signed char &a = acc[n][m][dl];
    if (a >= 0) return a;
    if (n == NT) return a = (m == MT);
    a = 0;
    for (int d = 0; d <= dl + 1 && d <= n; d++) {
        int m2 = m + d;
        if (m2 > MT) break;
        if (n + 1 < (int)(sizeof UBAR / sizeof *UBAR) && m2 > UBAR[n + 1] && !(n + 1 == NT)) continue;
        if (d * (n + 1) > 2 * m2) continue;
        if (accessible(n + 1, m2, d)) { a = 1; break; }
    }
    return a;
}

static unsigned long long compte[MAXN][128], noeuds;
static FILE *sortie;
static void ecrit_g6(int n, const u32 *adj) {
    char buf[128]; int p = 0; buf[p++] = 63 + n;
    int bit = 0, cur = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) { cur = cur << 1 | (adj[i] >> j & 1); if (++bit == 6) { buf[p++] = 63 + cur; bit = cur = 0; } }
    if (bit) buf[p++] = 63 + (cur << (6 - bit));
    buf[p] = 0; fprintf(sortie, "%s\n", buf);
}

static void etend(int n, int m, const u32 *adj, int prof) {
    noeuds++;
    compte[n][m]++;
    if (n == NT) { if (m == MT) ecrit_g6(n, adj); return; }
    int deg[MAXN], dl = 99;
    for (int i = 0; i < n; i++) { deg[i] = __builtin_popcount(adj[i]); dl = std::min(dl, deg[i]); }
    if (n == 0) dl = 0;
    int dvalides[8], nd = 0, dmax = -1;
    for (int d = 0; d <= dl + 1 && d <= n; d++) {
        int m2 = m + d;
        if (d * (n + 1) > 2 * m2 || m2 > MT) continue;
        if (n + 1 != NT && n + 1 < (int)(sizeof UBAR / sizeof *UBAR) && m2 > UBAR[n + 1]) continue;
        if (!accessible(n + 1, m2, d)) continue;
        // le nouveau sommet doit être de degré minimal : tous les sommets de degré d-1 sont ses voisins
        int oblig = 0; for (int i = 0; i < n; i++) if (deg[i] < d) oblig++;
        if (dl < d - 1 || oblig > d) continue;
        dvalides[nd++] = d; dmax = d;
    }
    if (!nd) return;
    Mauvais mv;
    nH = n; memcpy(adjH, adj, sizeof(u32) * n); memcpy(degH, deg, sizeof(int) * n);
    mauvais_voisinages(mv, dmax);
    std::set<std::string> locaux;
    for (int k = 0; k < nd; k++) {
        int d = dvalides[k];
        u32 oblig = 0; for (int i = 0; i < n; i++) if (deg[i] < d) oblig |= 1u << i;
        // voisinages N de taille d contenant oblig, sans ensemble interdit, implications respectées
        std::vector<u32> cands;
        {
            int reste = d - __builtin_popcount(oblig);
            // parcours des sommets par indice croissant ; un ensemble interdit est testé quand son plus grand sommet entre
            struct Niv { int i; u32 N; int r; };
            std::vector<Niv> pile{{0, 0, reste}};
            while (!pile.empty()) {
                Niv e = pile.back(); pile.pop_back();
                int i = e.i;
                if (i == n) {
                    if (e.r) continue;
                    bool ok = true;
                    for (auto &pr : mv.impl) if ((pr.first & e.N) == pr.first && !(e.N >> pr.second & 1)) { ok = false; break; }
                    if (ok) cands.push_back(e.N);
                    continue;
                }
                int libresApres = 0; for (int j = i; j < n; j++) if (!(oblig >> j & 1)) libresApres++;
                if (e.r > libresApres) continue;
                bool ob = oblig >> i & 1;
                if (!ob) pile.push_back({i + 1, e.N, e.r});               // sans le sommet i
                if (ob || e.r > 0) {
                    u32 N2 = e.N | 1u << i; bool ok = true;
                    for (u32 T : mv.parMax[i]) if ((T & N2) == T) { ok = false; break; }
                    if (ok) pile.push_back({i + 1, N2, e.r - (ob ? 0 : 1)});
                }
            }
        }
        std::vector<u32> appris;      // ensembles purs découverts en testant les candidats
        for (u32 N : cands) {
            bool rej = false;
            for (u32 T : appris) if ((T & N) == T) { rej = true; break; }
            if (rej) continue;
            nH = n; memcpy(adjH, adj, sizeof(u32) * n); memcpy(degH, deg, sizeof(int) * n);   // les appels récursifs les écrasent
            u32 Tp;
            if (candidat_interdit(N, Tp)) { if (Tp) appris.push_back(Tp); continue; }
            int n2 = n + 1;
            u32 a2[MAXN];
            for (int i = 0; i < n; i++) a2[i] = adj[i] | ((N >> i & 1) << n);
            a2[n] = N;
            // forme canonique et orbites
            graph g[MAXN], cg[MAXN]; int lab[MAXN], ptn[MAXN], orbits[MAXN];
            static DEFAULTOPTIONS_GRAPH(options); statsblk stats;
            options.getcanon = TRUE; options.defaultptn = FALSE;
            EMPTYGRAPH(g, 1, n2);
            for (int i = 0; i < n2; i++) for (u32 x = a2[i]; x; x &= x - 1) ADDELEMENT(GRAPHROW(g, i, 1), __builtin_ctz(x));
            // partition initiale par degré (invariante), pour accélérer nauty
            int dg[MAXN]; for (int i = 0; i < n2; i++) dg[i] = __builtin_popcount(a2[i]);
            for (int i = 0; i < n2; i++) lab[i] = i;
            std::sort(lab, lab + n2, [&](int x, int y) { return dg[x] != dg[y] ? dg[x] < dg[y] : x < y; });
            for (int i = 0; i < n2; i++) ptn[i] = (i + 1 < n2 && dg[lab[i]] == dg[lab[i + 1]]) ? 1 : 0;
            densenauty(g, lab, ptn, orbits, &options, &stats, 1, n2, cg);
            // parent canonique : premier sommet de degré minimal dans l'ordre canonique (lab[0], la partition
            // étant triée par degré croissant et le nouveau sommet étant de degré minimal)
            if (orbits[lab[0]] != orbits[n]) continue;
            std::string cle((const char *)cg, sizeof(graph) * n2);
            if (!locaux.insert(cle).second) continue;
            if (MOD && prof + 1 == PROF) { static unsigned long long rang = 0; if ((int)(rang++ % MOD) != RES) continue; }
            etend(n2, m + d, a2, prof + 1);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage : ud N M [tu] [stats] [part R MOD P]\n"); return 1; }
    NT = atoi(argv[1]); MT = atoi(argv[2]);
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "tu")) TU = true;
        else if (!strcmp(argv[i], "stats")) STATS = true;
        else if (!strcmp(argv[i], "part") && i + 3 < argc) { RES = atoi(argv[i + 1]); MOD = atoi(argv[i + 2]); PROF = atoi(argv[i + 3]); i += 3; }
    }
    FILE *f = fopen("forbidden.txt", "r");
    if (!f) { fprintf(stderr, "forbidden.txt introuvable\n"); return 1; }
    char ligne[1024]; int nF = 0;
    while (fgets(ligne, sizeof ligne, f)) {
        if (ligne[0] == '#') continue;
        int k, e, off = 0, used;
        if (sscanf(ligne, "%d %d%n", &k, &e, &used) != 2) continue;
        off = used;
        u32 a[10] = {0};
        for (int i = 0; i < e; i++) { int x, y; sscanf(ligne + off, "%d %d%n", &x, &y, &used); off += used; a[x] |= 1u << y; a[y] |= 1u << x; }
        BASE = nF < 2;       // K4 et K2,3, les deux premiers de la liste
        for (int p = 0; p < k; p++) ajoute_motif(k, a, p, -1, -1, -1);
        nF++;
    }
    fclose(f);
    int nMotF = motifs.size();
    BASE = false;
    if (TU) {
        // six motifs totalement infidèles (arXiv:2412.11914, figure 1) : arêtes, puis la paire forcée (x, y)
        static const int tu[6][40] = {
            {6, 8, 0,1, 1,2, 1,3, 4,2, 3,4, 5,4, 5,0, 5,3, /*paire*/ 0,2},
            {7, 11, 0,1, 2,1, 2,3, 4,3, 0,5, 2,5, 4,5, 0,2, 4,2, 6,3, 2,6, 1,6},
            {7, 11, 0,1, 2,3, 4,3, 0,5, 2,5, 4,5, 0,2, 4,2, 1,6, 6,3, 2,6, 1,2},
            {8, 12, 0,1, 2,0, 0,3, 1,4, 5,1, 5,4, 5,2, 6,4, 7,2, 7,3, 6,7, 6,5, 2,3},
            {8, 12, 0,1, 2,0, 0,3, 1,4, 5,1, 5,4, 5,2, 6,4, 7,2, 7,3, 6,7, 6,5, 4,3},
            {8, 11, 0,1, 2,0, 0,3, 1,4, 5,1, 5,2, 6,4, 7,2, 7,3, 6,7, 6,5, 4,3}};
        for (int t = 0; t < 6; t++) {
            int k = tu[t][0], e = tu[t][1]; u32 a[10] = {0};
            for (int i = 0; i < e; i++) { int x = tu[t][2 + 2 * i], y = tu[t][3 + 2 * i]; a[x] |= 1u << y; a[y] |= 1u << x; }
            int x = tu[t][2 + 2 * e], y = tu[t][3 + 2 * e];
            for (int p = 0; p < k; p++) {
                if (p == x) ajoute_motif(k, a, p, -1, -1, y);
                else if (p == y) ajoute_motif(k, a, p, -1, -1, x);
                else ajoute_motif(k, a, p, x, y, -1);
            }
        }
    }
    for (int i = 0; i < (int)motifs.size(); i++) ordreMotifs.push_back(i);
    std::stable_sort(ordreMotifs.begin(), ordreMotifs.end(), [](int x, int y) { return motifs[x].nS != motifs[y].nS ? motifs[x].nS < motifs[y].nS : motifs[x].k < motifs[y].k; });
    memset(acc, -1, sizeof acc);
    sortie = stdout;
    fprintf(stderr, "cible (%d, %d), %d graphes interdits, %d motifs d'extension%s\n", NT, MT, nF, nMotF, TU ? ", filtre totalement infidèle" : "");
    u32 vide[MAXN] = {0};
    etend(0, 0, vide, 0);
    fprintf(stderr, "graphes (%d, %d) : %llu ; nœuds visités : %llu\n", NT, MT, compte[NT][MT], noeuds);
    if (STATS) for (int n = 1; n <= NT; n++) for (int m = 0; m < 128; m++) if (compte[n][m]) fprintf(stderr, "  niveau %d, %d arêtes : %llu\n", n, m, compte[n][m]);
    return 0;
}
