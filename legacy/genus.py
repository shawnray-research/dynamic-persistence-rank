"""
genus.py -- validation for the bounded-genus repair theorem.

Claim (Theorem: bounded-genus repair):
  If K is a 2-complex in which every edge lies in <=2 triangles and which embeds in a surface of
  genus g, then D_1(K, M) is a digraph of genus <= g.  Reason: an arc (s,t)->(s',t') of D_1 requires
  s' to be an edge shared by triangles t and t', so D_1's underlying graph is a SUB-DIGRAPH of the
  dual graph G* (triangles = nodes, shared-edge = adjacency).  G* embeds in the same surface, so
  genus(D_1) <= genus(G*) <= g.  Then Sun (APPROX 2024) gives an O(g+1)-approximation for DFVS on
  genus-(g) digraphs, hence a constant-factor repair for fixed g, beating the general O(log eta).

This script checks, on random matchings of:
  * planar complexes (triangulated grids, octahedron = S^2): D_1 is a sub-digraph of the dual AND
    is planar (genus 0);
  * a torus (genus 1): D_1 is a sub-digraph of the dual (so genus(D_1) <= 1 by the embedding theorem).
"""

from __future__ import annotations
import random
import networkx as nx
from ph_predictions import closure, pair_digraph, random_matching, is_matching


def tri_grid(m, k):
    """m x k triangulated grid (planar; every interior edge in exactly two triangles)."""
    tris = []
    for i in range(m - 1):
        for j in range(k - 1):
            a, b, c, d = (i, j), (i + 1, j), (i, j + 1), (i + 1, j + 1)
            tris.append(frozenset([a, b, d]))
            tris.append(frozenset([a, d, c]))
    return closure(tris)


def octahedron():
    v = [('p', i) for i in range(6)]
    T = [(0, 2, 4), (2, 1, 4), (1, 3, 4), (3, 0, 4),
         (0, 2, 5), (2, 1, 5), (1, 3, 5), (3, 0, 5)]
    return closure([frozenset([v[a], v[b], v[c]]) for a, b, c in T])


def torus(m, k):
    """Flat torus triangulation (genus 1); every edge in exactly two triangles. Needs m,k >= 3."""
    tris = []
    for i in range(m):
        for j in range(k):
            a = (i % m, j % k); b = ((i + 1) % m, j % k)
            c = ((i + 1) % m, (j + 1) % k); d = (i % m, (j + 1) % k)
            tris.append(frozenset([a, b, c])); tris.append(frozenset([a, c, d]))
    return closure(tris)


def d1_graph(M):
    nodes, adj = pair_digraph(M, p=1)
    idx = {nd: i for i, nd in enumerate(nodes)}
    G = nx.Graph(); G.add_nodes_from(range(len(nodes)))
    sub_ok = True
    for u in nodes:
        for v in adj[u]:
            if len(u[1] & v[1]) != 2:      # arc must join triangles sharing an edge (dual adjacency)
                sub_ok = False
            G.add_edge(idx[u], idx[v])
    return nodes, G, sub_ok


def check(K, label, rng, want_planar, ntrials=80):
    sub = planar = trials = 0
    for _ in range(ntrials):
        M = random_matching(K, density=rng.uniform(0.4, 1.0), rng=rng)
        if not is_matching(M):
            continue
        nodes, G, sub_ok = d1_graph(M)
        if len(nodes) < 3:
            continue
        trials += 1
        sub += sub_ok
        planar += nx.check_planarity(G)[0]
    flag = "planar(g=0)" if want_planar else "genus<=1"
    extra = f"  D1 planar: {planar}/{trials}" if want_planar else ""
    print(f"{label:16s} trials={trials:3d}  D1 sub-digraph of dual: {sub}/{trials}   [{flag}]{extra}")
    return sub == trials and (planar == trials or not want_planar)


if __name__ == "__main__":
    rng = random.Random(0)
    allok = True
    print("=== Bounded-genus: D_1 is a sub-digraph of the dual; planar => genus 0 ===")
    for (m, k) in [(3, 3), (4, 3), (4, 4), (5, 4)]:
        allok &= check(tri_grid(m, k), f"tri-grid {m}x{k}", rng, want_planar=True)
    allok &= check(octahedron(), "octahedron S^2", rng, want_planar=True)
    allok &= check(torus(3, 3), "torus T^2 (g=1)", rng, want_planar=False)
    allok &= check(torus(4, 3), "torus T^2 (g=1)", rng, want_planar=False)
    print(f"\nBOUNDED-GENUS VALIDATED: {allok}")
    if allok:
        print("=> genus(D_1) <= genus(K); Sun'24 gives O(g+1)-approx repair for embeddable 2-complexes.")
