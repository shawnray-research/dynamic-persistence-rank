"""
hardness.py  --  the NP-hardness reduction for Open Problem 1, with computational validation.

Claim (Theorem, to be written up only if validated here):
  Computing dfvs(D_1) over pair-digraphs of 2-complexes is NP-hard, because Directed Feedback
  Vertex Set on out-degree-<=2 digraphs (NP-hard) reduces to it: given such a digraph G, we build a
  2-complex K(G) with matching M such that dfvs(D_1(K(G), M)) = dfvs(G).

Construction (single wires; NO doubling needed):
  * Vertex gadget: for each v, a triangle t_v = {a_v,b_v,c_v} with matched edge e_v = {a_v,b_v}.
    Node N_v = (e_v, t_v) in D_1.  Its two free edges {b_v,c_v}, {a_v,c_v} start v's <=2 out-wires.
  * Arc gadget: arc (u->v) is a triangle strip (wire) from a free edge of t_u to e_v = {a_v,b_v},
    realizing a directed path N_u -> ... -> N_v in D_1, with all-fresh interior vertices.

Why single wires suffice (no doubling):
  Deleting a wire-internal node breaks exactly the D_1-cycles through that arc (= arc deletion in G);
  deleting N_v = vertex deletion in G. So dfvs(D_1) = min MIXED vertex/arc feedback set of G. But
  min mixed = dfvs(G): replace each deleted arc (u->v) by deleting u; this removes >= as many cycles
  at equal cost (G minus the new vertex set is a subgraph of G minus the mixed set, hence acyclic).
  Therefore dfvs(D_1(K(G))) = dfvs(G).

This script verifies that identity on many random out-degree-<=2 digraphs.
"""

from __future__ import annotations
import random, itertools
from ph_predictions import closure, pair_digraph, digraph_has_cycle, is_matching, faces


# ----------------------------- bounded-search exact DFVS -----------------------------
# Feasible whenever the feedback number is small, even if the digraph is large.

def _find_cycle(nodes, adj):
    color = {u: 0 for u in nodes}
    parent = {}
    def dfs(u):
        color[u] = 1
        for v in adj[u]:
            if v not in color:        # v removed
                continue
            if color[v] == 1:         # back-edge: reconstruct cycle v..u
                cyc = [u]; x = u
                while x != v:
                    x = parent[x]; cyc.append(x)
                return cyc
            if color[v] == 0:
                parent[v] = u
                r = dfs(v)
                if r: return r
        color[u] = 2
        return None
    for s in nodes:
        if color[s] == 0:
            r = dfs(s)
            if r: return r
    return None


def _dfvs_bounded(nodes, adj, k):
    cyc = _find_cycle(nodes, adj)
    if cyc is None:
        return set()
    if k == 0:
        return None
    for v in cyc:
        rem = nodes - {v}
        adj2 = {u: [w for w in adj[u] if w in rem] for u in rem}
        sol = _dfvs_bounded(rem, adj2, k - 1)
        if sol is not None:
            return sol | {v}
    return None


def exact_dfvs(nodes, adj):
    nodes = set(nodes)
    adj = {u: [w for w in adj[u] if w in nodes] for u in nodes}
    for k in range(0, len(nodes) + 1):
        s = _dfvs_bounded(set(nodes), adj, k)
        if s is not None:
            return k
    return len(nodes)


def dfvs_of_digraph(V, arcs):
    nodes = set(V)
    adj = {u: [] for u in nodes}
    for (u, v) in arcs:
        adj[u].append(v)
    return exact_dfvs(nodes, adj)


# ----------------------------- the reduction G |-> K(G) ------------------------------

def build_complex_from_digraph(V, arcs):
    """Return (K, matching). Assumes out-degree <= 2 at every vertex."""
    a = {v: ("a", v) for v in V}
    b = {v: ("b", v) for v in V}
    c = {v: ("c", v) for v in V}
    triangles, matching = [], []
    for v in V:
        t_v = frozenset([a[v], b[v], c[v]])
        e_v = frozenset([a[v], b[v]])
        triangles.append(t_v); matching.append((e_v, t_v))
    free = {v: [frozenset([b[v], c[v]]), frozenset([a[v], c[v]])] for v in V}
    used = {v: 0 for v in V}
    fid = itertools.count()
    for (u, w) in arcs:
        assert used[u] < 2, "out-degree > 2 not supported"
        fe = free[u][used[u]]; used[u] += 1
        z0, z1 = tuple(fe)                          # matched edge {z0,z1} = free edge of t_u
        p2, p3 = ("p", next(fid)), ("p", next(fid)) # fresh interior vertices
        zs = [z0, z1, p2, p3, a[w], b[w]]           # z_0 .. z_5 ; e_w = {a_w,b_w} = {z_4,z_5}
        for i in range(0, 4):                       # triangles t_i = {z_i,z_{i+1},z_{i+2}}
            ti = frozenset([zs[i], zs[i + 1], zs[i + 2]])
            ei = frozenset([zs[i], zs[i + 1]])      # matched edge {z_i,z_{i+1}} <-> t_i
            triangles.append(ti); matching.append((ei, ti))
    K = closure(triangles)
    return K, matching


def D1_of(K, M):
    nodes, adj = pair_digraph(M, p=1)
    return nodes, adj


# ------------- out-degree reduction (Lemma: general DFVS -> out-degree-2, exact) ------
# Path-of-out-copies: vertex v with out-neighbors w_1..w_q becomes a directed path
# v^(0)->...->v^(q-1); all in-arcs enter v^(0); v^(i-1) emits the arc to w_i (into w_i^(0)).
# The internal paths are acyclic, so dfvs(split(G)) == dfvs(G), and a FVS of split(G)
# projects (v^(i) -> v) to one of G of no greater size.  This lets the hardness reduction
# start from GENERAL (Karp) DFVS, making it self-contained and optimum-preserving.

def outdeg2_split(V, arcs):
    out = {v: [] for v in V}
    for (u, w) in arcs:
        out[u].append(w)
    newV, rep0, raw = [], {}, []
    for v in V:
        q = max(len(out[v]), 1)
        copies = [(v, i) for i in range(q)]
        newV += copies
        rep0[v] = copies[0]
        for i in range(len(copies) - 1):
            raw.append((copies[i], copies[i + 1]))       # internal acyclic path
        for i, w in enumerate(out[v]):
            raw.append((copies[i], ("TO", w)))           # external arc, redirect below
    arcs2 = [(a, (rep0[b[1]] if isinstance(b, tuple) and b and b[0] == "TO" else b))
             for (a, b) in raw]
    return newV, arcs2


def random_general_digraph(k, rng, p=0.45):
    """Arbitrary digraph (unbounded out-degree) -- the source of the self-contained reduction."""
    V = list(range(k))
    arcs = [(u, v) for u in V for v in V if u != v and rng.random() < p]
    return V, arcs


# ----------------------------- validation -------------------------------------------

def random_outdeg2_digraph(k, rng):
    V = list(range(k))
    arcs = []
    for u in V:
        outdeg = rng.choice([0, 1, 1, 2, 2])
        targets = [v for v in V if v != u]
        rng.shuffle(targets)
        for v in targets[:outdeg]:
            arcs.append((u, v))
    # dedupe parallel arcs (keep simple)
    seen, uniq = set(), []
    for e in arcs:
        if e not in seen:
            seen.add(e); uniq.append(e)
    return V, uniq


def validate(trials=400, seed=0, verbose=True):
    rng = random.Random(seed)
    ok = mism = 0
    max_eta = 0
    cyclic = 0
    for t in range(trials):
        k = rng.randint(3, 7)
        V, arcs = random_outdeg2_digraph(k, rng)
        dG = dfvs_of_digraph(V, arcs)
        K, M = build_complex_from_digraph(V, arcs)
        assert is_matching(M), "constructed matching invalid"
        nodes, adj = D1_of(K, M)
        # structural sanity: out-degree <= 2, no 2-cycle (Cor 2)
        idx = {nd: i for i, nd in enumerate(nodes)}
        for u in nodes:
            assert len(adj[u]) <= 2, "out-degree > 2 in D_1!"
            for v in adj[u]:
                assert u not in adj[v], "2-cycle in D_1 (violates girth>=3)"
        dD = exact_dfvs(nodes, adj)
        if dD == dG:
            ok += 1
        else:
            mism += 1
            if verbose and mism <= 5:
                print(f"  MISMATCH: dfvs(G)={dG} dfvs(D1)={dD}  G={V},{arcs}")
        max_eta = max(max_eta, dG)
        if dG > 0:
            cyclic += 1
    print(f"[validate] trials={trials}  dfvs(D1)==dfvs(G): {ok}/{ok+mism}   "
          f"(cyclic G: {cyclic}, max dfvs seen: {max_eta})")
    return mism == 0


def validate_general(trials=400, seed=0, verbose=True):
    """Self-contained reduction from GENERAL DFVS: split G to out-degree two (Lemma), then build
       K(G').  Confirms both optimum-preserving identities used by the NP-hardness and the
       inapproximability (Thm: approximation essentially optimal):
          dfvs(split(G)) == dfvs(G)            and       dfvs(D_1(K(split(G)))) == dfvs(G)."""
    rng = random.Random(seed)
    ok_split = ok_comp = total = 0
    for _ in range(trials):
        k = rng.randint(3, 6)
        V, arcs = random_general_digraph(k, rng)
        dG = dfvs_of_digraph(V, arcs)
        Vs, arcs2 = outdeg2_split(V, arcs)
        assert max([sum(1 for (a, b) in arcs2 if a == x) for x in Vs] + [0]) <= 2
        if dfvs_of_digraph(Vs, arcs2) == dG:
            ok_split += 1
        K, M = build_complex_from_digraph(Vs, arcs2)
        assert is_matching(M)
        nodes, adj = D1_of(K, M)
        if exact_dfvs(nodes, adj) == dG:
            ok_comp += 1
        total += 1
    print(f"[general] dfvs(split(G))==dfvs(G): {ok_split}/{total}   "
          f"dfvs(D1(K(split(G))))==dfvs(G): {ok_comp}/{total}")
    return ok_split == total and ok_comp == total


if __name__ == "__main__":
    print("=== Validating dfvs(D_1(K(G))) == dfvs(G) on random out-deg<=2 digraphs ===")
    allok = True
    for s in range(5):
        allok &= validate(trials=300, seed=s, verbose=True)
    print("\n=== Self-contained from GENERAL DFVS: split to out-degree two, then build K(G') ===")
    for s in range(5):
        allok &= validate_general(trials=300, seed=100 + s, verbose=True)
    print(f"\nREDUCTION VALIDATED (optimum-preserving): {allok}")
    if allok:
        print("=> repair (dfvs of D_1) is NP-hard for d>=2, and inherits DFVS inapproximability.")
