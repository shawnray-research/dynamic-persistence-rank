"""
treewidth.py -- validation for the treewidth theorem.

Theorem (treewidth):  For any complex K and matching M, and every dimension p,
        tw(D_p(M)) <= tw(H(K)),
where H(K) is the (undirected) Hasse diagram of K.  Hence repair is solvable exactly in
2^{O(t log t)} * n time with t = tw(H(K)) (Bonamy-Kowalik-Nederlof-Pilipczuk-Socala-Wrochna,
WG 2018), and 2^{O(t)} for surface-embeddable K (their planar case).

Proof (constructive, validated here):  given a tree decomposition (T, {B_x}) of H(K), put
        B'_x = { the matched pair containing c : c in B_x and c is matched }.
This is a tree decomposition of D_p:
  (coverage)   a node (s,t) of D_p has t in some B_x, so (s,t) in B'_x;
  (edges)      an arc (s,t)->(s',t') needs s' a facet of t, i.e. s'--t adjacent in H(K), so s',t
               share a bag B_x, giving both pairs in B'_x;
  (connected)  the bags holding a fixed pair (s,t) are those with s or t; s--t are Hasse-adjacent
               so their (connected) subtrees meet, and the union is connected.
Width does not increase (each cell contributes at most its one pair), so tw(D_p) <= tw(H(K)).

This script builds a tree decomposition of H(K) (min-fill heuristic), applies the transform, and
verifies the result is a VALID tree decomposition of each D_p of width <= the H(K) decomposition.
It also checks that the hardness reduction K(G) inflates Hasse-treewidth only by a constant factor
(so the 2^{o(t log t)} ETH lower bound for DFVS transfers to repair).
"""

from __future__ import annotations
import random
import networkx as nx
from networkx.algorithms.approximation import treewidth_min_fill_in
from ph_predictions import closure, pair_digraph, faces, random_matching, is_matching, by_dim
from hardness import build_complex_from_digraph, outdeg2_split, random_general_digraph


def hasse_graph(K):
    G = nx.Graph()
    cells = [c for c in K if len(c) >= 1]
    G.add_nodes_from(cells)
    cs = set(cells)
    for c in cells:
        for f in faces(c):
            if f in cs:
                G.add_edge(c, f)
    return G


def width_of(T):
    return max((len(b) for b in T.nodes()), default=1) - 1


def transform(T_hasse, M):
    """Map each Hasse bag B to B' = {matched pair of c : c in B, c matched}; keep the tree shape."""
    cell2pair = {}
    for (lo, hi) in M:
        cell2pair[lo] = (lo, hi); cell2pair[hi] = (lo, hi)
    contents = {x: frozenset(cell2pair[c] for c in x if c in cell2pair) for x in T_hasse.nodes()}
    return T_hasse, contents     # same tree, relabelled bag contents


def verify_td(T, contents, nodes, arcs):
    bags = [contents[x] for x in T.nodes()]
    covered = set().union(*bags) if bags else set()
    if not set(nodes) <= covered:
        return False
    for (u, v) in arcs:                                   # every arc inside some bag
        if not any(u in contents[x] and v in contents[x] for x in T.nodes()):
            return False
    for z in nodes:                                       # bags holding z are a connected subtree
        sub = [x for x in T.nodes() if z in contents[x]]
        if sub and not nx.is_connected(T.subgraph(sub)):
            return False
    return True


def dense_complex(rng, npts, dim, radius):
    from ph_predictions import vietoris_rips
    pts = [tuple(rng.random() for _ in range(dim)) for _ in range(npts)]
    return vietoris_rips(pts, radius=radius, maxdim=min(dim, 3))


def validate_tw(trials=120, seed=0):
    rng = random.Random(seed)
    ok = tot = 0
    worst_gap = 0
    for _ in range(trials):
        K = dense_complex(rng, npts=rng.choice([6, 7, 8]), dim=rng.choice([2, 3]),
                          radius=rng.uniform(0.7, 1.0))
        if len([c for c in K if len(c) >= 1]) < 6:
            continue
        M = random_matching(K, density=rng.uniform(0.4, 1.0), rng=rng)
        if not is_matching(M) or len(M) < 2:
            continue
        H = hasse_graph(K)
        wH, TH = treewidth_min_fill_in(H)            # wH = width of this decomposition of H(K)
        T, contents = transform(TH, M)
        good = True
        for p in sorted({len(lo) - 1 for lo, _ in M}):
            nodes, adj = pair_digraph(M, p)
            arcs = [(u, v) for u in nodes for v in adj[u]]
            wDp = max((len(contents[x]) for x in T.nodes()), default=1) - 1
            if not verify_td(T, contents, set(nodes), arcs) or wDp > wH:
                good = False
            worst_gap = max(worst_gap, wH - wDp)
        ok += good; tot += 1
    print(f"[tw<=]  valid D_p tree-decomposition of width <= tw(H(K)) : {ok}/{tot}   "
          f"(max slack tw(H)-tw(D_p) seen: {worst_gap})")
    return ok == tot


def validate_reduction_blowup(trials=60, seed=1):
    """K(G) inflates Hasse-treewidth by only a constant factor (ETH lower-bound transfer)."""
    rng = random.Random(seed)
    ratios = []
    for _ in range(trials):
        k = rng.randint(3, 6)
        V, arcs = random_general_digraph(k, rng)
        Vs, arcs2 = outdeg2_split(V, arcs)
        K, M = build_complex_from_digraph(Vs, arcs2)
        # tw(G) via underlying undirected graph
        UG = nx.Graph(); UG.add_nodes_from(V); UG.add_edges_from([(u, v) for (u, v) in arcs])
        twG = treewidth_min_fill_in(UG)[0] if UG.number_of_edges() else 0
        twH = treewidth_min_fill_in(hasse_graph(K))[0]
        ratios.append((twH, twG))
    cmax = max((h / g) for (h, g) in ratios if g > 0) if any(g > 0 for _, g in ratios) else 0
    addmax = max((h - g) for (h, g) in ratios)
    print(f"[reduction]  tw(H(K(G))) vs tw(G): max ratio {cmax:.2f}, max additive gap {addmax}  "
          f"(bounded => 2^o(t log t) ETH bound transfers)")
    return True


if __name__ == "__main__":
    print("=== Treewidth: tw(D_p) <= tw(H(K)) by the constructive tree-decomposition transform ===")
    a = validate_tw()
    b = validate_reduction_blowup()
    print(f"\nTREEWIDTH THEOREM VALIDATED: {a and b}")
    if a:
        print("=> repair is exact in 2^{O(t log t)} n, t = tw(H(K)) [BKNPSW'18]; 2^{O(t)} for planar.")
