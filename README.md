# At most 60 unit distances among 22 points in the plane: u(22) = 60

Let u(n) be the largest number of pairs at distance exactly 1 among n points in the plane (Erdős's
unit distance problem, [OEIS A186705](https://oeis.org/A186705)). The values u(n) are known for
n ≤ 21 (Schade; Ágoston and Pálvölgyi; Alexeev, Mixon and Parshall,
[arXiv:2412.11914](https://arxiv.org/abs/2412.11914)), and 60 ≤ u(22) ≤ 61.

This repository contains a computation showing that **no unit-distance graph has 22 vertices and
61 edges, hence u(22) = 60**.

> **Status.** Not checked by a third party; novelty not confirmed. The enumeration relies on a
> **single implementation** (`enumeration/ud.cpp`); no independent second enumeration of the
> 61-edge case exists yet. The result also relies on two published lists that we did not re-prove:
> the 74 forbidden graphs of Globus and Parshall
> ([arXiv:1905.07829](https://arxiv.org/abs/1905.07829)) and the six "totally unfaithful" patterns
> of Alexeev, Mixon and Parshall. Corrections and pointers to prior work are welcome: please open
> an issue.

## Method

We follow the method of Alexeev, Mixon and Parshall, rewritten from scratch (their code is not
public).

1. **Enumeration.** Generate, up to isomorphism, all graphs with 22 vertices and 61 edges that
   contain none of the 74 minimal forbidden graphs on at most 9 vertices of Globus and Parshall
   (`enumeration/forbidden.txt`, extracted from the Sage notebook attached to their paper). Graphs
   are built vertex by vertex, the added vertex having minimum degree in the new graph, with
   McKay's canonical augmentation (nauty); a reachability table on (vertices, edges, minimum
   degree) prunes branches that cannot reach the target.
2. **Totally unfaithful patterns at every level.** One may assume that the graph sought is the
   *full* unit-distance graph of its point set (adding missing unit pairs only increases the number
   of edges). Every induced subgraph is then also a full unit-distance graph, so none contains a
   pattern forcing two non-adjacent vertices to be at distance 1. The paper applies this filter at
   the last level only; applying it at every level divides the number of nodes by 3 to 4.
3. **Rhombus certificates.** In an embedding with distinct points, every 4-cycle (a, b, c, d) of
   unit edges is a rhombus, so f(a) + f(c) = f(b) + f(d). If a rational combination of these linear
   equations gives f(u) = f(v) for two distinct vertices, the graph is not a unit-distance graph.

## Result

| Target | Nodes visited | Graphs left after steps 1–2 |
|---|---|---|
| 22 vertices, 62 edges | 40,680,983 | 0 (as in the paper) |
| 22 vertices, 61 edges | 607,851,252 (64 parts, 242 core-hours) | **3** |

The three surviving graphs (`results/survivors_22_61.g6`, graph6 format) are **not** unit-distance
graphs: for each of them `results/rhombus_certificates.txt` gives an explicit combination of 12 to
15 rhombus equations, with coefficients ±1, ±1/2, ±1/3, ±1/6 or 3/2, forcing two vertices to
coincide. The certificate can be checked by hand. `results/parts_22_61.txt` lists the node count
and running time of each of the 64 parts.

Validation of the enumeration against Table 1 of Alexeev, Mixon and Parshall (number of graphs
with n vertices and u(n) edges): identical without the filter for n = 5 to 19, and with the filter
for n = 17 to 21 (8, 38, 5, 1, 19 graphs).

## Verify

```bash
python3 verification/rhombus_certificate.py results/survivors_22_61.g6
```

The script (Python 3, no dependency) recomputes, in exact rational arithmetic, a certificate for
each graph and re-checks it by direct summation. It only proves that these three graphs are not
unit-distance graphs; it does not re-check that the enumeration is exhaustive.

To recompute the enumeration: build [nauty](https://pallini.di.uniroma1.it/) 2.8.9 next to
`ud.cpp`, then

```bash
cd enumeration
g++ -O2 -march=native -I nauty2_8_9 -o ud ud.cpp nauty2_8_9/nauty.a
./ud 21 57 tu stats > g21.g6          # 19 graphs, about 25 core-hours
./ud 22 61 tu stats part 0 64 12      # part 0 of 64, split at depth 12
```

Comments and messages in `ud.cpp` are in French.

*Résumé en français : aucun graphe de distances unité n'a 22 sommets et 61 arêtes, donc u(22) = 60.
Énumération des graphes sans sous-graphe interdit ni motif totalement infidèle (608 millions de
nœuds), 3 graphes restants, tous exclus par un certificat exact « tout cycle de longueur 4 est un
losange ». Une seule implémentation de l'énumération ; pas encore vérifié par un tiers ; nouveauté
non confirmée.*

## Licence

Code: MIT (`LICENSE`). Data: CC BY 4.0 (`LICENSE-DATA.md`). `enumeration/forbidden.txt` is derived
from the notebook of Globus and Parshall. Written with the help of Claude.
