"""anyR3.py -- Corollary cor:anyR3 (compressed dual graph). For a universe U that is a proper subcomplex of a triangulated
3-sphere T (so ||U|| lies in R^3), the outer cells are the components of S^3 minus ||U||. The multigraph G(K) has the outer
cells and the tetrahedra of U as nodes and one edge per triangle t of U not in K, joining the nodes on the two sides of t.
Claim: beta_3(K) = 0 and beta_2(K) = c(G(K)) - n_3(K) - 1 for every subcomplex K of U (checked against brute force over F_2)."""
import random
from itertools import combinations

def closure(gens):
    K = set()
    for s in gens:
        s = tuple(sorted(s))
        for k in range(1, len(s) + 1):
            for f in combinations(s, k):
                K.add(frozenset(f))
    return K

def f2_rank(rows):
    piv = {}; rk = 0
    for r in rows:
        r = set(r)
        while r:
            p = max(r)
            if p in piv: r ^= piv[p]
            else: piv[p] = r; rk += 1; break
    return rk

def boundary_rank(cells, p):
    lower = [c for c in cells if len(c) == p]; upper = [c for c in cells if len(c) == p + 1]
    idx = {c: i for i, c in enumerate(lower)}
    return f2_rank([{idx[c - {v}] for v in c if (c - {v}) in idx} for c in upper])

def betti(cells):
    n = [len([c for c in cells if len(c) == d + 1]) for d in range(4)]
    r = [boundary_rank(cells, d + 1) for d in range(4)]
    return (n[0] - r[0], n[1] - r[0] - r[1], n[2] - r[1] - r[2], n[3] - r[2] - r[3])

def comps(nodes, edges):
    par = {v: v for v in nodes}
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for a, b in edges: par[f(a)] = f(b)
    return len({f(v) for v in nodes}), f

def join_cycles(m, n):
    a = list(range(m)); b = list(range(m, m + n))
    return [frozenset((a[i], a[(i + 1) % m], b[j], b[(j + 1) % n])) for i in range(m) for j in range(n)]

def maximal(K):
    return [s for s in K if not any(s < t for t in K if len(t) == len(s) + 1)]

rng = random.Random(11); ok = tot = 0; nontriv = 0
for trial in range(240):
    m, n = rng.randint(3, 5), rng.randint(3, 5)
    tets = join_cycles(m, n); T = closure(tets)
    tri_cof = {}
    for t in tets:
        for f in combinations(sorted(t), 3): tri_cof.setdefault(frozenset(f), []).append(t)
    # universe U: a proper subcomplex of T (random deletions of maximal simplices / random closure)
    if rng.random() < 0.5:
        U = set(T)
        for _ in range(1 + rng.randint(0, len(T) // 2)):
            mx = maximal(U)
            if not mx: break
            U.discard(rng.choice(mx))
    else:
        U = closure([s for s in T if rng.random() < [0.4, 0.35, 0.35, 0.25][len(s) - 1]])
    if U == T or not U: continue
    # outer cells: components of T-tetrahedra not in U, joined through T-triangles not in U
    out_t = [t for t in tets if t not in U]
    e = [tuple(tri_cof[f]) for f in tri_cof if f not in U]
    _, find = comps(out_t, [(a, b) for a, b in e if a not in U and b not in U])
    def side_node(tau):
        return ('tet', tau) if tau in U else ('out', find(tau))
    U_tets = [t for t in tets if t in U]
    nodes = {('tet', t) for t in U_tets} | {('out', find(t)) for t in out_t}
    for _ in range(6):
        # random subcomplex K of U
        K = set(U)
        for _ in range(rng.randint(0, len(U))):
            mx = maximal(K)
            if not mx: break
            K.discard(rng.choice(mx))
        edges = []
        for f in tri_cof:
            if f in U and f not in K:
                a, b = tri_cof[f]; edges.append((side_node(a), side_node(b)))
        cG, _ = comps(nodes, edges)
        n3 = len([s for s in K if len(s) == 4])
        b = betti(K)
        tot += 1; nontriv += b[2] > 0
        ok += (b[3] == 0) and (b[2] == cG - n3 - 1)
print(f"compressed dual graph formula beta_2(K) = c(G(K)) - n_3(K) - 1 and beta_3 = 0: {ok}/{tot} ({nontriv} cases with beta_2 > 0)")
print("ALL VALIDATED:", ok == tot)
