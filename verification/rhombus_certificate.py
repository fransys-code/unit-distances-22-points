"""Preuve exacte de non-plongeabilité par les losanges. Dans un plongement en distances unité (points distincts), tout
cycle de longueur 4 (a, b, c, d) est un losange : f(a) + f(c) = f(b) + f(d). Si ces équations linéaires entraînent
f(u) = f(v) pour deux sommets distincts, le graphe n'est pas plongeable. Calcul en rationnels exacts.
Usage : losanges.py FICHIER.g6 ; affiche pour chaque graphe une paire forcée à coïncider et la combinaison qui le prouve."""
import sys
from fractions import Fraction

def lit_g6(s):
    s = s.strip(); n = ord(s[0]) - 63
    bits = []
    for c in s[1:]:
        v = ord(c) - 63
        bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    E = []; t = 0
    for j in range(1, n):
        for i in range(j):
            if bits[t]: E.append((i, j))
            t += 1
    return n, E


def cycles4(n, E):
    adj = [set() for _ in range(n)]
    for i, j in E: adj[i].add(j); adj[j].add(i)
    L = []
    for a in range(n):
        for c in range(a + 1, n):
            co = sorted(adj[a] & adj[c])
            for x in range(len(co)):
                for y in range(x + 1, len(co)): L.append((a, co[x], c, co[y]))
    return L


def paire_forcee(n, E):
    L = cycles4(n, E)
    # élimination de Gauss sur [A | I] pour garder la combinaison de lignes
    M = []
    for r, (a, b, c, d) in enumerate(L):
        v = [Fraction(0)] * n; v[a] += 1; v[c] += 1; v[b] -= 1; v[d] -= 1
        M.append((v, {r: Fraction(1)}))
    base = []                      # (pivot, vecteur, combinaison)
    for v, comb in M:
        for p, w, cw in base:
            if v[p]:
                t = v[p] / w[p]
                v = [x - t * y for x, y in zip(v, w)]
                for k, q in cw.items(): comb[k] = comb.get(k, 0) - t * q
        p = next((i for i, x in enumerate(v) if x), None)
        if p is not None: base.append((p, v, comb))
    def reduit(v):
        comb = {}
        for p, w, cw in base:
            if v[p]:
                t = v[p] / w[p]
                v = [x - t * y for x, y in zip(v, w)]
                for k, q in cw.items(): comb[k] = comb.get(k, 0) + t * q
        return v, comb
    for u in range(n):
        for w in range(u + 1, n):
            v = [Fraction(0)] * n; v[u] = 1; v[w] = -1
            r, comb = reduit(v)
            if not any(r):
                comb = {k: q for k, q in comb.items() if q}
                # contrôle direct : somme des q·(e_a + e_c − e_b − e_d) = e_u − e_w
                s = [Fraction(0)] * n
                for k, q in comb.items():
                    a, b, c, d = L[k]; s[a] += q; s[c] += q; s[b] -= q; s[d] -= q
                assert s == [Fraction(int(i == u) - int(i == w)) for i in range(n)]
                return (u, w), [(L[k], q) for k, q in sorted(comb.items())], len(L), len(base)
    return None, None, len(L), len(base)


if __name__ == "__main__":
    for k, l in enumerate(open(sys.argv[1])):
        if not l.strip(): continue
        n, E = lit_g6(l)
        paire, preuve, nc, rang = paire_forcee(n, E)
        if paire is None:
            print(f"{k} {l.strip()} n={n} m={len(E)} : {nc} cycles de longueur 4, rang {rang}, AUCUNE paire forcée")
        else:
            print(f"{k} {l.strip()} n={n} m={len(E)} : {nc} cycles de longueur 4, rang {rang}, NON PLONGEABLE : sommets {paire[0]} et {paire[1]} confondus")
            print("   preuve : " + " ".join(f"{'+' if q > 0 else '-'}{abs(q) if abs(q) != 1 else ''}{c}" for c, q in preuve))
