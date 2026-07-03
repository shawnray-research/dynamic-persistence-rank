"""
gadgets.py -- toward Open Problem 1 (is repairing a prediction NP-hard for d>=2?).

We attempt to realize arbitrary directed-feedback-vertex-set structure inside the pair-digraph
D_1 of a 2-complex, by building primitives (wire, branch, merge) from triangle strips and
VALIDATING (with the harness) that D_1 is exactly the intended digraph -- no unintended arcs/cycles.

This is exploratory: a primitive is only useful if `pair_digraph` confirms its structure.
"""

from __future__ import annotations
from collections import defaultdict
from ph_predictions import (
    faces, closure, pair_digraph, digraph_has_cycle, is_matching,
    modified_hasse_cycle, min_dfvs_bruteforce,
)


def wire(zs):
    """Triangle strip on vertices zs=[z0,...,z_{L+2}]:
        triangles t_i = {z_i,z_{i+1},z_{i+2}},  matched edge e_i={z_i,z_{i+1}} <-> t_i.
       Realizes a directed path p_0->p_1->...->p_L in D_1.
       Returns (simplices, matching, node_list_in_path_order)."""
    L = len(zs) - 3  # last triangle index
    tris, M, nodes = [], [], []
    for i in range(0, L + 1):
        t = frozenset([zs[i], zs[i + 1], zs[i + 2]])
        e = frozenset([zs[i], zs[i + 1]])
        tris.append(t)
        M.append((e, t))
        nodes.append((e, t))
    K = closure(tris)
    return K, M, nodes


def describe_digraph(M, p=1):
    nodes, adj = pair_digraph(M, p)
    idx = {nd: i for i, nd in enumerate(nodes)}
    arcs = [(idx[u], idx[v]) for u in nodes for v in adj[u]]
    outdeg = {idx[u]: len(adj[u]) for u in nodes}
    return nodes, adj, idx, arcs, outdeg


def validate_wire(L=5):
    zs = list(range(L + 3))
    K, M, nodes = wire(zs)
    assert is_matching(M), "wire matching invalid"
    nds, adj, idx, arcs, outdeg = describe_digraph(M, p=1)
    arcs_sorted = sorted(arcs)
    expected = sorted((i, i + 1) for i in range(len(nodes) - 1))
    ok_path = (arcs_sorted == expected)
    ok_acyclic = not digraph_has_cycle(nds, adj)
    ok_outdeg = all(outdeg[idx[nd]] <= 1 for nd in nds)
    print(f"[wire L={L}] #nodes={len(nds)} arcs={arcs_sorted}")
    print(f"   is a clean directed path: {ok_path};  acyclic: {ok_acyclic};  out-deg<=1: {ok_outdeg}")
    # also confirm the direct modified-Hasse view agrees on acyclicity
    assert modified_hasse_cycle(K, M) == (not ok_acyclic)
    return ok_path and ok_acyclic and ok_outdeg


def make_3cycle_via_wires():
    """Sanity: glue three wires head-to-tail with shared endpoint edges to form ONE directed
       cycle in D_1, and check dfvs=1. (Tests that wires compose and that we control cycles.)
       We reuse the tetra-minus-face gadget as the minimal closed example."""
    a, b, c, d = 0, 1, 2, 3
    tris = [frozenset([a, b, c]), frozenset([b, c, d]), frozenset([a, b, d])]
    K = closure(tris)
    M = [(frozenset([a, b]), frozenset([a, b, c])),
         (frozenset([b, c]), frozenset([b, c, d])),
         (frozenset([b, d]), frozenset([a, b, d]))]
    nds, adj = pair_digraph(M, 1)
    print(f"[3-cycle] nodes={len(nds)} cyclic={digraph_has_cycle(nds, adj)} "
          f"dfvs={min_dfvs_bruteforce(nds, adj)}")
    return digraph_has_cycle(nds, adj) and min_dfvs_bruteforce(nds, adj) == 1


if __name__ == "__main__":
    print("=== validating the WIRE primitive (triangle strip -> directed path in D_1) ===")
    allok = True
    for L in [1, 2, 3, 5, 8]:
        allok &= validate_wire(L)
    print("\n=== validating cycle control ===")
    allok &= make_3cycle_via_wires()
    print(f"\nALL PRIMITIVE CHECKS PASSED: {allok}")
