#!/usr/bin/env python3
"""s3.py -- verification of the query formulas of the fully dynamic S^3 algorithm (thm:s3, lem:dual).

Universe T: a triangulated 3-sphere, given by its tetrahedra.  Tested triangulations:
  * the join C_m * C_n of two cycles (vertices a_0..a_{m-1}, b_0..b_{n-1}; tetrahedra
    {a_i, a_{i+1}, b_j, b_{j+1}}, indices mod m and mod n; m, n >= 3), several (m, n);
  * the boundary of the 4-simplex (5 tetrahedra) and of the 4-dimensional cross-polytope (16 tetrahedra);
  * irregular triangulations obtained from C_4 * C_5 and from the 4-simplex boundary by random stellar
    subdivisions (of tetrahedra, triangles and edges).

Claimed formulas, for a subcomplex K of T:
  K == T (equivalently n_3(K) == n_3(T), T being pure):  (beta_0, beta_1, beta_2, beta_3) = (1, 0, 0, 1);
  otherwise  beta_0 = c(G_0(K))            [G_0(K) = (vertices of K, edges of K)],
             beta_3 = 0,
             beta_2 = c(G_*(K)) - n_3(K) - 1  [G_*(K): vertex set = ALL tetrahedra of T, one edge per triangle
                                               of T not in K joining the two tetrahedra that contain it],
             beta_1 = beta_0 + beta_2 - chi(K),  chi = n_0 - n_1 + n_2 - n_3.
Everything is compared with brute-force Betti numbers (ranks of boundary matrices) over F_2, and on samples over
F_3 and F_5 with oriented boundaries.  Lemma lem:dual (c(G_*(K)) - n_3(K) = number of components of S^3 - |K|)
is checked independently: S^3 - |K| deformation retracts onto the order complex of the up-set T - K (its
simplices are the chains of that poset), so its components are the components of the Hasse graph of T - K.
The dynamic checks simulate the algorithm itself: counters n_q, and component counts of G_0 and G_* maintained
only through the O(1) graph updates of the update rules plus connectivity queries (as a dynamic connectivity
structure would supply them); the answer after EVERY operation is compared with brute force.
Standard library only.  Run:  python3 s3.py
"""
from __future__ import annotations
import random
import sys
from itertools import combinations

# ---- self-contained helpers (copied from the repository's dynrank.py and churn.py) ----
def f2_rank(rows):
    piv = {}
    rk = 0
    for r in rows:
        r = set(r)
        while r:
            p = max(r)
            if p in piv:
                r ^= piv[p]
            else:
                piv[p] = r
                rk += 1
                break
    return rk


def boundary_rank(cells, p):
    """rank of d_p : C_p -> C_{p-1} for the complex given as a set of frozensets."""
    lower = [c for c in cells if len(c) == p]
    upper = [c for c in cells if len(c) == p + 1]
    idx = {c: i for i, c in enumerate(lower)}
    cols = [{idx[frozenset(c - {v})] for v in c if frozenset(c - {v}) in idx} for c in upper]
    return f2_rank(cols)


def betti(cells):
    n = [len([c for c in cells if len(c) == d + 1]) for d in range(4)]
    r = [boundary_rank(cells, d + 1) for d in range(4)]   # r[0]=rank d1, r[1]=rank d2, ...
    b0 = n[0] - r[0]
    b1 = (n[1] - r[0]) - r[1]
    b2 = (n[2] - r[1]) - r[2]
    b3 = (n[3] - r[2]) - r[3]
    return b0, b1, b2, b3


def matrix_rank(A):
    if not A or not A[0]:
        return 0
    return f2_rank([{j for j, x in enumerate(row) if x} for row in A])


def cylinder(a, b):
    """Annulus between 3-cycles a,b (vertex triples): 6 triangles, boundary a+b."""
    m = len(a)
    return ([(a[i], a[(i + 1) % m], b[i]) for i in range(m)]
            + [(a[(i + 1) % m], b[i], b[(i + 1) % m]) for i in range(m)])


def disk(a, ctr):
    """Cap the 3-cycle a with center vertex ctr: 3 triangles, boundary a."""
    return [(ctr, a[i], a[(i + 1) % len(a)]) for i in range(len(a))]


def fp_rank(rows, p):
    """rank over F_p; rows: list of dict col->coeff."""
    rows = [dict(r) for r in rows]
    piv = {}
    rk = 0
    for r in rows:
        r = {c: v % p for c, v in r.items() if v % p}
        while r:
            j = max(r)
            if j in piv:
                pr = piv[j]
                mult = (r[j] * pow(pr[j], -1, p)) % p
                r = {c: (r.get(c, 0) - mult * pr.get(c, 0)) % p
                     for c in set(r) | set(pr)}
                r = {c: v for c, v in r.items() if v}
            else:
                piv[j] = r
                rk += 1
                break
    return rk


def oriented_d2_rank(cells, p):
    """rank over F_p of the oriented triangle-edge boundary of a complex given as frozensets."""
    tris = [tuple(sorted(c)) for c in cells if len(c) == 3]
    edges = [tuple(sorted(c)) for c in cells if len(c) == 2]
    ei = {e: i for i, e in enumerate(edges)}
    rows = []
    for (a, b, c) in tris:
        rows.append({ei[(b, c)]: 1, ei[(a, c)]: -1, ei[(a, b)]: 1})
    return fp_rank(rows, p)
# ---- end helpers ----

betti_f2 = betti  # brute-force F_2 Betti numbers (boundary ranks)

RESULTS = []


def report(name, ok, detail=""):
    RESULTS.append(bool(ok))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  -- {detail}" if detail else ""))


# ------------------------------------------------------------------------------------------------
# complexes
# ------------------------------------------------------------------------------------------------

def closure(gens):
    K = set()
    for s in gens:
        s = tuple(sorted(s))
        for k in range(1, len(s) + 1):
            for f in combinations(s, k):
                K.add(frozenset(f))
    return K


def skey(s):
    return (len(s), sorted(s))


def chi(K):
    return sum((-1) ** (len(s) - 1) for s in K)


def counts(K):
    n = [0, 0, 0, 0]
    for s in K:
        n[len(s) - 1] += 1
    return n


def betti_fp(K, p):
    """Brute-force Betti numbers over F_p with the oriented boundary d[v_0..v_q] = sum_i (-1)^i [.. v_i^ ..]."""
    by_dim = [sorted(tuple(sorted(s)) for s in K if len(s) == d + 1) for d in range(4)]
    idx = [{s: i for i, s in enumerate(L)} for L in by_dim]
    rk = [0, 0, 0, 0, 0]                    # rk[d] = rank of d_d : C_d -> C_{d-1}
    for d in range(1, 4):
        rows = []
        for s in by_dim[d]:
            rows.append({idx[d - 1][s[:i] + s[i + 1:]]: (-1) ** i % p for i in range(len(s))})
        rk[d] = fp_rank(rows, p)
    return tuple(len(by_dim[d]) - rk[d] - rk[d + 1] for d in range(4))


def component_labels(vertices, edges):
    parent = {v: v for v in vertices}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for u, w in edges:
        ru, rw = find(u), find(w)
        if ru != rw:
            parent[ru] = rw
    return {v: find(v) for v in parent}


def components(vertices, edges):
    return len(set(component_labels(vertices, edges).values()))


class Sphere:
    """A triangulated 3-sphere given by its list of tetrahedra."""

    def __init__(self, name, tets):
        self.name = name
        self.tets = sorted({frozenset(t) for t in tets}, key=skey)
        assert all(len(t) == 4 for t in self.tets)
        self.T = closure(self.tets)
        self.Tlist = sorted(self.T, key=skey)
        self.tri_cof = {}
        for t in self.tets:
            for f in combinations(sorted(t), 3):
                self.tri_cof.setdefault(frozenset(f), []).append(t)
        self.up = {s: [] for s in self.T}          # codimension-1 cofaces in T
        for s in self.T:
            for v in s:
                f = s - {v}
                if f:
                    self.up[f].append(s)
        self.N3 = len(self.tets)

    def dual_edge(self, tri):
        x, y = self.tri_cof[tri]
        return x, y


def join_cycles(m, n):
    a = list(range(m))
    b = list(range(m, m + n))
    return [(a[i], a[(i + 1) % m], b[j], b[(j + 1) % n]) for i in range(m) for j in range(n)]


def simplex4_boundary():
    return list(combinations(range(5), 4))


def cross_polytope4_boundary():
    # vertices 2k (= +e_k) and 2k+1 (= -e_k); facets choose one sign per coordinate
    return [tuple(2 * k + s[k] for k in range(4)) for s in
            [(x, y, z, w) for x in (0, 1) for y in (0, 1) for z in (0, 1) for w in (0, 1)]]


def stellar(tets, sigma, v):
    """Stellar subdivision of the simplex sigma at the new vertex v (on the facet list)."""
    sigma = frozenset(sigma)
    out = []
    for t in tets:
        t = frozenset(t)
        if sigma <= t:
            out.extend((t - {w}) | {v} for w in sigma)
        else:
            out.append(t)
    return out


def random_stellar(tets, k, rng):
    tets = [frozenset(t) for t in tets]
    for _ in range(k):
        T = sorted(closure(tets), key=skey)
        cand = [s for s in T if len(s) >= 2]
        sigma = rng.choice(cand)
        v = max(max(t) for t in tets) + 1
        tets = stellar(tets, sigma, v)
    return tets


# ------------------------------------------------------------------------------------------------
# the claimed query formulas (static evaluation) and an independent count for lem:dual
# ------------------------------------------------------------------------------------------------

def formula(S, K):
    n = counts(K)
    if n[3] == S.N3:                               # K == T
        return (1, 0, 0, 1)
    V = [next(iter(s)) for s in K if len(s) == 1]
    E = [tuple(s) for s in K if len(s) == 2]
    b0 = components(V, E)
    dual = [S.dual_edge(t) for t in S.tri_cof if t not in K]
    cstar = components(S.tets, dual)
    b2 = cstar - n[3] - 1
    b1 = b0 + b2 - (n[0] - n[1] + n[2] - n[3])
    return (b0, b1, b2, 0)


def dual_count(S, K):
    """c(G_*(K)) - n_3(K), plus sanity of the structure used in the proof of lem:dual."""
    dual = [S.dual_edge(t) for t in S.tri_cof if t not in K]
    for x, y in dual:                              # every dual edge joins two tetrahedra not in K
        assert x not in K and y not in K
    return components(S.tets, dual) - counts(K)[3]


def complement_components(S, K):
    """Components of the Hasse graph of the up-set T - K (= components of S^3 - |K|)."""
    rest = [s for s in S.T if s not in K]
    edges = [(s, c) for s in rest for c in S.up[s]]   # cofaces of s are not in K either
    return components(rest, edges)


# ------------------------------------------------------------------------------------------------
# checks on the universes
# ------------------------------------------------------------------------------------------------

def link(S, s):
    return {c - s for c in S.T if s < c}


def is_2sphere(L):
    tris = [t for t in L if len(t) == 3]
    edges = [e for e in L if len(e) == 2]
    if not tris:
        return False
    cnt = {e: 0 for e in edges}
    for t in tris:
        for e in combinations(sorted(t), 2):
            cnt[frozenset(e)] += 1
    if any(c != 2 for c in cnt.values()):
        return False                               # not a closed surface
    if components([next(iter(v)) for v in L if len(v) == 1], [tuple(e) for e in edges]) != 1:
        return False
    return chi(L) == 2                             # closed connected surface with chi 2 = S^2


def is_circle(L):
    verts = [next(iter(v)) for v in L if len(v) == 1]
    edges = [tuple(e) for e in L if len(e) == 2]
    deg = {v: 0 for v in verts}
    for u, w in edges:
        deg[u] += 1
        deg[w] += 1
    return len(verts) >= 3 and all(d == 2 for d in deg.values()) and components(verts, edges) == 1


def check_universe(S):
    pm = (set(S.tri_cof) == {s for s in S.T if len(s) == 3}
          and all(len(v) == 2 for v in S.tri_cof.values()))
    strongly = components(S.tets, [S.dual_edge(t) for t in S.tri_cof]) == 1
    vlinks = all(is_2sphere(link(S, s)) for s in S.T if len(s) == 1)
    elinks = all(is_circle(link(S, s)) for s in S.T if len(s) == 2)
    # for every simplex sigma of dim <= 2: the tetrahedra containing sigma are connected through the triangles
    # containing sigma (the fact used in the injectivity part of the proof of lem:dual)
    stars = all(components([t for t in S.tets if s <= t],
                           [S.dual_edge(f) for f in S.tri_cof if s <= f]) == 1 for s in S.T if len(s) <= 3)
    b2, b3 = betti_f2(S.T), betti_fp(S.T, 3)
    ok = (pm and strongly and vlinks and elinks and stars and chi(S.T) == 0
          and b2 == (1, 0, 0, 1) and b3 == (1, 0, 0, 1))
    n = counts(S.T)
    report(f"universe {S.name}: f-vector {tuple(n)}", ok,
           f"closed pseudomanifold={pm}, dual graph connected={strongly}, vertex links S^2={vlinks}, "
           f"edge links S^1={elinks}, stars dual-connected={stars}, chi={chi(S.T)}, betti F2={b2}, F3={b3}")
    return ok


# ------------------------------------------------------------------------------------------------
# random subcomplexes
# ------------------------------------------------------------------------------------------------

def maximal_simplices(S, K):
    return [s for s in sorted(K, key=skey) if not any(c in K for c in S.up[s])]


def gen_closure(S, rng):
    p = [rng.uniform(0, 0.6), rng.uniform(0, 0.5), rng.uniform(0, 0.45), rng.uniform(0, 0.3)]
    return closure([s for s in S.Tlist if rng.random() < p[len(s) - 1]])


def gen_delete_maximal(S, rng):
    K = set(S.T)
    r = 1 + int(len(S.T) * rng.random() ** 2)
    for _ in range(r):
        mx = maximal_simplices(S, K)
        if not mx:
            break
        K.discard(rng.choice(mx))
    return K


def gen_remove_open_stars(S, rng):
    seeds = rng.sample(S.Tlist, rng.randint(1, 6))
    return {s for s in S.T if not any(q <= s for q in seeds)}


def gen_hollow(S, rng):
    hollow = rng.sample(S.tets, rng.randint(1, max(1, S.N3 // 2)))
    filled = rng.sample(S.tets, rng.randint(0, S.N3 // 3))
    gens = [frozenset(f) for t in hollow for f in combinations(sorted(t), 3)] + filled
    extra = [s for s in S.Tlist if len(s) <= 2 and rng.random() < 0.1]
    return closure(gens + extra)


def gen_skeleton_minus(S, rng):
    K = {s for s in S.T if len(s) <= 3} | set(rng.sample(S.tets, rng.randint(0, S.N3)))
    for _ in range(rng.randint(0, len(S.T) // 3)):
        mx = maximal_simplices(S, K)
        if not mx:
            break
        K.discard(rng.choice(mx))
    return K


GENERATORS = [("closure", gen_closure), ("delete-maximal", gen_delete_maximal),
              ("remove-open-stars", gen_remove_open_stars), ("hollow-tetrahedra", gen_hollow),
              ("2-skeleton-minus", gen_skeleton_minus)]


def is_subcomplex(S, K):
    return K <= S.T and all((s - {v}) in K for s in K if len(s) > 1 for v in s)


def check_static(S, K, fields=()):
    """Return (formula ok, lem:dual ok, field ok, betti)."""
    assert is_subcomplex(S, K)
    b = betti_f2(K)
    ok = formula(S, K) == b
    dual_ok = True
    if K != S.T:
        d = dual_count(S, K)
        dual_ok = (d == complement_components(S, K)) and (b[2] == d - 1) and (b[3] == 0)
    field_ok = all(betti_fp(K, p) == b for p in fields)
    return ok, dual_ok, field_ok, b


# ------------------------------------------------------------------------------------------------
# the dynamic algorithm (simulated with the update rules of thm:s3)
# ------------------------------------------------------------------------------------------------

class Graph:
    """Multigraph with connectivity queries (stand-in for a dynamic connectivity structure)."""

    def __init__(self, vertices=()):
        self.adj = {v: {} for v in vertices}

    def add_vertex(self, v):
        assert v not in self.adj
        self.adj[v] = {}

    def remove_vertex(self, v):
        assert not self.adj[v]
        del self.adj[v]

    def add_edge(self, u, w):
        self.adj[u][w] = self.adj[u].get(w, 0) + 1
        self.adj[w][u] = self.adj[w].get(u, 0) + 1

    def remove_edge(self, u, w):
        for x, y in ((u, w), (w, u)):
            self.adj[x][y] -= 1
            if not self.adj[x][y]:
                del self.adj[x][y]

    def connected(self, u, w):
        seen, stack = {u}, [u]
        while stack:
            x = stack.pop()
            if x == w:
                return True
            for y in self.adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return False


class DynamicS3:
    def __init__(self, S):
        self.S = S
        self.K = set()
        self.n = [0, 0, 0, 0]
        self.G0 = Graph()
        self.c0 = 0
        self.Gs = Graph(S.tets)
        for t in S.tri_cof:                         # K = {} initially: every dual edge is present
            self.Gs.add_edge(*S.dual_edge(t))
        self.cs = components(S.tets, [S.dual_edge(t) for t in S.tri_cof])
        self.graph_changes = []                    # number of graph updates per simplex update

    def insert(self, s):
        assert s not in self.K and all((s - {v}) in self.K for v in s if len(s) > 1)
        self.K.add(s)
        self.n[len(s) - 1] += 1
        ch = 0
        if len(s) == 1:
            self.G0.add_vertex(next(iter(s)))
            self.c0 += 1
            ch = 1
        elif len(s) == 2:
            u, w = tuple(s)
            if not self.G0.connected(u, w):
                self.c0 -= 1
            self.G0.add_edge(u, w)
            ch = 1
        elif len(s) == 3:
            x, y = self.S.dual_edge(s)
            self.Gs.remove_edge(x, y)
            if not self.Gs.connected(x, y):
                self.cs += 1
            ch = 1
        self.graph_changes.append(ch)

    def delete(self, s):
        assert s in self.K and not any(c in self.K for c in self.S.up[s])
        self.K.discard(s)
        self.n[len(s) - 1] -= 1
        ch = 0
        if len(s) == 1:
            self.G0.remove_vertex(next(iter(s)))
            self.c0 -= 1
            ch = 1
        elif len(s) == 2:
            u, w = tuple(s)
            self.G0.remove_edge(u, w)
            if not self.G0.connected(u, w):
                self.c0 += 1
            ch = 1
        elif len(s) == 3:
            x, y = self.S.dual_edge(s)
            if not self.Gs.connected(x, y):
                self.cs -= 1
            self.Gs.add_edge(x, y)
            ch = 1
        self.graph_changes.append(ch)

    def query(self):
        n = self.n
        if n[3] == self.S.N3:
            return (1, 0, 0, 1)
        b2 = self.cs - n[3] - 1
        return (self.c0, self.c0 + b2 - (n[0] - n[1] + n[2] - n[3]), b2, 0)


def run_dynamic(S, ops, rng, start_full=False, f3_every=10):
    D = DynamicS3(S)
    if start_full:
        for s in S.Tlist:
            D.insert(s)
    stats = dict(ops=0, ins=0, dels=0, fail=0, f3=0, f3fail=0, dualfail=0, maxb=[0, 0, 0, 0], full=0, empty=0,
                 void=0, pure_fail=0)
    period = 2 * int(len(S.T) / 0.6) + rng.randint(0, 40)    # long enough to sweep empty <-> (nearly) full
    ops = max(ops, int(1.25 * period))
    for step in range(ops):
        phase = (step % period) / period
        p_ins = 0.85 if phase < 0.5 else 0.2
        if start_full:
            p_ins = 1 - p_ins
        ins = [s for s in S.Tlist if s not in D.K and all((s - {v}) in D.K for v in s if len(s) > 1)]
        dels = maximal_simplices(S, D.K)
        do_ins = (rng.random() < p_ins and ins) or not dels
        if do_ins:
            D.insert(rng.choice(ins))
            stats['ins'] += 1
        else:
            D.delete(rng.choice(dels))
            stats['dels'] += 1
        stats['ops'] += 1
        b = betti_f2(D.K)
        q = D.query()
        if q != b or q != formula(S, D.K):
            stats['fail'] += 1
            if stats['fail'] <= 3:
                print(f"    FAIL step {step}: query={q} brute={b} static={formula(S, D.K)} n={D.n}")
        if D.K != S.T and dual_count(S, D.K) != complement_components(S, D.K):
            stats['dualfail'] += 1
        if step % f3_every == 0:
            stats['f3'] += 1
            if betti_fp(D.K, 3) != b:
                stats['f3fail'] += 1
        stats['maxb'] = [max(x, y) for x, y in zip(stats['maxb'], b)]
        stats['full'] += (D.K == S.T)
        stats['empty'] += (not D.K)
        stats['void'] += (b[2] > 0)
        stats['pure_fail'] += ((D.n[3] == S.N3) != (D.K == S.T))
    stats['maxchange'] = max(D.graph_changes)
    return stats


# ------------------------------------------------------------------------------------------------
# explicit cases
# ------------------------------------------------------------------------------------------------

def explicit_cases_join(m, n):
    """Named subcomplexes of C_m * C_n with their known (topologically expected) Betti numbers."""
    S = Sphere(f"C_{m}*C_{n}", join_cycles(m, n))
    a = list(range(m))
    b = list(range(m, m + n))
    T = S.T
    N = S.N3
    tau = S.tets[0]
    cases = []
    cases.append(("empty", set(), (0, 0, 0, 0)))
    cases.append(("full T", set(T), (1, 0, 0, 1)))
    cases.append(("single vertex", {frozenset({a[0]})}, (1, 0, 0, 0)))
    cases.append(("hollow tetrahedron (boundary of one tetrahedron)",
                  closure(combinations(sorted(tau), 3)), (1, 0, 1, 0)))
    cases.append(("T minus one tetrahedron (a 3-ball)", T - {tau}, (1, 0, 0, 0)))
    far = [t for t in S.tets if len(t & tau) <= 2][0]
    cases.append(("T minus two tetrahedra sharing no triangle (S^2 x I)", T - {tau, far}, (1, 0, 1, 0)))
    tri = sorted(S.tri_cof, key=skey)[0]
    x, y = S.dual_edge(tri)
    cases.append(("T minus two adjacent tetrahedra, common triangle kept", T - {x, y}, (1, 0, 1, 0)))
    cases.append(("T minus two adjacent tetrahedra and their common triangle", T - {x, y, tri}, (1, 0, 0, 0)))
    cases.append(("T minus open star of a vertex", {s for s in T if a[0] not in s}, (1, 0, 0, 0)))
    cases.append(("T minus open star of an edge", {s for s in T if not {a[0], a[1]} <= s}, (1, 0, 0, 0)))
    nV, nE = len([s for s in T if len(s) == 1]), len([s for s in T if len(s) == 2])
    cases.append(("2-skeleton of T", {s for s in T if len(s) <= 3}, (1, 0, N - 1, 0)))
    cases.append(("1-skeleton of T", {s for s in T if len(s) <= 2}, (1, nE - nV + 1, 0, 0)))
    Cm = closure([(a[i], a[(i + 1) % m]) for i in range(m)])
    Cn = closure([(b[j], b[(j + 1) % n]) for j in range(n)])
    cases.append(("core circle C_m", Cm, (1, 1, 0, 0)))
    cases.append(("Hopf link C_m u C_n", Cm | Cn, (2, 2, 0, 0)))
    cases.append(("T minus open star of C_m (= C_n)", {s for s in T if not (s & set(a))}, (1, 1, 0, 0)))
    typeA = closure([(a[i], a[(i + 1) % m], b[j]) for i in range(m) for j in range(n)])
    typeB = closure([(a[i], b[j], b[(j + 1) % n]) for i in range(m) for j in range(n)])
    cases.append(("all triangles {a_i,a_i+1,b_j} (= C_m * n points)", typeA, (1, 0, n - 1, 0)))
    cases.append(("all triangles {a_i,b_j,b_j+1} (= C_n * m points)", typeB, (1, 0, m - 1, 0)))
    cases.append(("all triangles {a_i,a_i+1,b_j} and {a_i,b_j,b_j+1} (= the 2-skeleton)",
                  typeA | typeB, (1, 0, N - 1, 0)))
    other = [t for t in S.tets if not (t & tau)]
    if other:
        cases.append(("two vertex-disjoint hollow tetrahedra",
                      closure(list(combinations(sorted(tau), 3)) + list(combinations(sorted(other[0]), 3))),
                      (2, 0, 2, 0)))
    if m == n and m >= 4:
        def strip(d):
            return [(a[i], a[(i + 1) % m], b[(i + d) % n]) for i in range(m)] + \
                   [(a[(i + 1) % m], b[(i + d) % n], b[(i + d + 1) % n]) for i in range(m)]
        cases.append(("annulus strip (zigzag a_0 b_0 a_1 b_1 ...), boundary C_m u C_n",
                      closure(strip(0)), (1, 1, 0, 0)))
        torus = closure(strip(0) + strip(2))
        cases.append(("torus = union of two disjoint-interior strips", torus, (1, 2, 1, 0)))
        lab = component_labels(S.tets, [S.dual_edge(t) for t in S.tri_cof if t not in torus])
        sides = {}
        for t in S.tets:
            sides.setdefault(lab[t], []).append(t)
        assert len(sides) == 2, "the torus separates S^3 into two regions"
        for k, side in enumerate(sorted(sides.values(), key=len)):
            cases.append((f"solid side {k + 1} of the torus (closure of its {len(side)} tetrahedra)",
                          closure(side), (1, 1, 0, 0)))
    return S, cases


def torus_is_torus(S, K):
    """K is a closed orientable surface with chi 0: each edge in 2 triangles, vertex links circles, F3-betti (1,2,1)."""
    tris = [t for t in K if len(t) == 3]
    cnt = {}
    for t in tris:
        for e in combinations(sorted(t), 2):
            cnt[frozenset(e)] = cnt.get(frozenset(e), 0) + 1
    surf = all(c == 2 for c in cnt.values()) and len(cnt) == len([e for e in K if len(e) == 2])
    vl = all(is_circle({c - s for c in K if s < c}) for s in K if len(s) == 1)
    return surf and vl and chi(K) == 0 and betti_fp(K, 3) == (1, 2, 1, 0)


# ------------------------------------------------------------------------------------------------

def main():
    rng = random.Random(20261102)
    rng_tri = random.Random(7)
    spheres = [Sphere("C_3*C_3", join_cycles(3, 3)), Sphere("C_3*C_5", join_cycles(3, 5)),
               Sphere("C_4*C_4", join_cycles(4, 4)), Sphere("C_4*C_6", join_cycles(4, 6)),
               Sphere("C_5*C_5", join_cycles(5, 5)),
               Sphere("boundary of 4-simplex", simplex4_boundary()),
               Sphere("boundary of 4-cross-polytope", cross_polytope4_boundary()),
               Sphere("stellar(C_4*C_5, 6 random subdivisions)", random_stellar(join_cycles(4, 5), 6, rng_tri)),
               Sphere("stellar(boundary 4-simplex, 8 random subdivisions)",
                      random_stellar(simplex4_boundary(), 8, rng_tri))]

    print("== (s) self-test of the brute-force routines on RP^2 (6 vertices; not a subcomplex of any S^3) ==")
    rp2 = closure([(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 5, 1),
                   (1, 2, 4), (2, 3, 5), (3, 4, 1), (4, 5, 2), (5, 1, 3)])
    f2, f3 = betti_f2(rp2), betti_fp(rp2, 3)
    report("(s) RP^2: F_2 Betti (1,1,1,0), F_3 Betti (1,0,0,0) -- so the F_3 checks below have teeth",
           f2 == (1, 1, 1, 0) and f3 == (1, 0, 0, 0) and betti_fp(rp2, 2) == f2, f"F2={f2}, F3={f3}")
    print("== (0) the universes are triangulated 3-spheres (combinatorial closed 3-manifolds, Betti (1,0,0,1)) ==")
    for S in spheres:
        check_universe(S)

    print("== (a) random subcomplexes: formulas vs brute-force F_2 Betti numbers; lem:dual; F_3 sample ==")
    tot_cases = tot_fail = dual_fail = f3_cnt = f3_fail = 0
    seen_b = set()
    for S in spheres:
        s_tot = s_fail = s_dual = s_f3 = 0
        s_seen = set()
        for gname, gen in GENERATORS:
            for k in range(7):
                K = gen(S, rng)
                fields = (3,) if k % 2 == 0 else ()
                ok, dok, fok, b = check_static(S, K, fields)
                s_tot += 1
                s_fail += not ok
                s_dual += not dok
                s_f3 += not fok
                f3_cnt += len(fields)
                s_seen.add(b)
        seen_b |= s_seen
        tot_cases += s_tot
        tot_fail += s_fail
        dual_fail += s_dual
        f3_fail += s_f3
        report(f"(a) {s_tot} random subcomplexes of {S.name}", s_fail == s_dual == s_f3 == 0,
               f"formula failures={s_fail}, lem:dual failures={s_dual}, F3 failures={s_f3}, "
               f"distinct Betti vectors={len(s_seen)}, max b2={max(b[2] for b in s_seen)}, "
               f"max b1={max(b[1] for b in s_seen)}")
    report(f"(a) {tot_cases} random subcomplexes ({len(spheres)} universes x {len(GENERATORS)} generators x 7): "
           f"formula == brute force F_2", tot_fail == 0, f"failures={tot_fail}")
    report("(a) lem:dual: c(G_*) - n_3 == #components of S^3 - |K| (Hasse graph of T - K); beta_2 == that - 1; "
           "beta_3 == 0 (K != T)", dual_fail == 0, f"failures={dual_fail}")
    report(f"(a) field independence: F_3 brute force == F_2 brute force on {f3_cnt} of them",
           f3_fail == 0, f"failures={f3_fail}")
    mx = [max(b[i] for b in seen_b) for i in range(4)]
    print(f"     distinct Betti vectors seen: {len(seen_b)}; max (b0,b1,b2,b3) = {tuple(mx)}; "
          f"#with b2>0: {sum(1 for b in seen_b if b[2] > 0)} vectors")

    print("== (b) random dynamic sequences: simulated algorithm (update rules + connectivity) vs brute force "
          "after EVERY operation ==")
    dyn_specs = [(spheres[0], 300, False), (spheres[1], 300, True), (spheres[2], 300, False),
                 (spheres[3], 300, False), (spheres[4], 300, True), (spheres[5], 300, False),
                 (spheres[6], 300, False), (spheres[7], 300, False), (spheres[8], 300, True)]
    all_dyn_ok = True
    total_ops = 0
    for S, ops, full in dyn_specs:
        st = run_dynamic(S, ops, rng, start_full=full)
        total_ops += st['ops']
        ok = (st['fail'] == 0 and st['dualfail'] == 0 and st['f3fail'] == 0 and st['maxchange'] <= 1
              and st['pure_fail'] == 0)
        all_dyn_ok &= ok
        report(f"(b) dynamic on {S.name}: {st['ops']} ops ({st['ins']} ins, {st['dels']} del), start "
               f"{'full' if full else 'empty'}", ok,
               f"answer!=brute: {st['fail']}, lem:dual fails: {st['dualfail']}, F3 checks {st['f3']} "
               f"(fails {st['f3fail']}), max graph updates/op {st['maxchange']}, max betti seen {tuple(st['maxb'])}, "
               f"#states K=T: {st['full']}, K=empty: {st['empty']}, beta_2>0: {st['void']}")
    print(f"     total dynamic operations checked: {total_ops}")

    print("== (c) explicit cases ==")
    for (m, n) in [(4, 4), (5, 5), (3, 4), (4, 6)]:
        S, cases = explicit_cases_join(m, n)
        for name, K, expect in cases:
            ok, dok, fok, b = check_static(S, K, (3, 5))
            good = ok and dok and fok and b == expect
            extra = ""
            if name.startswith("torus"):
                tt = torus_is_torus(S, K)
                good &= tt
                extra = f", is closed orientable surface with chi 0 (torus): {tt}"
            report(f"(c) C_{m}*C_{n}: {name}", good,
                   f"brute F2={b}, formula={formula(S, K)}, expected={expect}, F3/F5 agree={fok}{extra}")
    for S in [spheres[5], spheres[6], spheres[8]]:
        tau = S.tets[0]
        for name, K, expect in [("empty", set(), (0, 0, 0, 0)), ("full T", set(S.T), (1, 0, 0, 1)),
                                ("hollow tetrahedron", closure(combinations(sorted(tau), 3)), (1, 0, 1, 0)),
                                ("T minus one tetrahedron", S.T - {tau}, (1, 0, 0, 0)),
                                ("2-skeleton", {s for s in S.T if len(s) <= 3}, (1, 0, S.N3 - 1, 0))]:
            ok, dok, fok, b = check_static(S, K, (3, 5))
            report(f"(c) {S.name}: {name}", ok and dok and fok and b == expect,
                   f"brute F2={b}, formula={formula(S, K)}, expected={expect}")

    print("== (d) field independence over F_5 on a further sample ==")
    f5_fail = 0
    cnt = 0
    for S in spheres:
        for gname, gen in GENERATORS:
            K = gen(S, rng)
            cnt += 1
            if not (betti_fp(K, 5) == betti_f2(K) == formula(S, K)):
                f5_fail += 1
    report(f"(d) {cnt} random subcomplexes: F_5 brute force == F_2 brute force == formula", f5_fail == 0,
           f"failures={f5_fail}")

    print("== (e) negative controls: deliberately wrong variants of the formulas must be caught ==")

    def variant(S, K, kind):
        n = counts(K)
        if kind != "no K==T case" and n[3] == S.N3:
            return (1, 0, 0, 1)
        b0 = components([next(iter(s)) for s in K if len(s) == 1], [tuple(s) for s in K if len(s) == 2])
        tris = [t for t in S.tri_cof if (t in K) == (kind == "dual edges for triangles IN K")]
        c = components(S.tets, [S.dual_edge(t) for t in tris])
        b2 = c - n[3] - (0 if kind == "beta_2 without the -1" else 1)
        if kind == "G_* on tetrahedra not in K, n_3 still subtracted":
            c = components([t for t in S.tets if t not in K], [S.dual_edge(t) for t in tris])
            b2 = c - n[3] - 1
        return (b0, b0 + b2 - chi(K), b2, 0)

    pool = [(S, gen(S, rng)) for S in spheres for _, gen in GENERATORS for _ in range(2)]
    pool += [(S, set(S.T)) for S in spheres]
    for kind in ["no K==T case", "beta_2 without the -1", "dual edges for triangles IN K",
                 "G_* on tetrahedra not in K, n_3 still subtracted"]:
        caught = sum(variant(S, K, kind) != betti_f2(K) for S, K in pool)
        report(f"(e) wrong variant '{kind}' is detected", caught > 0, f"wrong on {caught}/{len(pool)} complexes")

    print(f"ALL VALIDATED: {all(RESULTS)}   ({sum(RESULTS)}/{len(RESULTS)} checks passed)")


if __name__ == "__main__":
    main()
