"""Flag/clique-complex transfer.
 (a) sd(K) = clique complex of the comparability graph of K's face poset; Betti numbers agree with K.
 (b) For a subcomplex K of a universe U: clique complex of the INDUCED subgraph of G_U on K = sd(K).
 (c) bounded vertex degree in the tube gadget universe => bounded degree of G_U (report max degree).
"""
import random, sys
from itertools import combinations
# ---- inlined F_2 homology helpers (from dynrank.py of the original verification suite) ----
from itertools import combinations

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


class Builder:
    def __init__(self):
        self.V = 0
        self.tris = set()
        self.edges = set()

    def fresh(self, n):
        xs = list(range(self.V, self.V + n))
        self.V += n
        return xs

    def add_tris(self, ts):
        for t in ts:
            t = frozenset(t)
            assert len(t) == 3
            self.tris.add(t)
            for e in combinations(sorted(t), 2):
                self.edges.add(frozenset(e))

    def add_loop(self, loop):
        for i in range(len(loop)):
            self.edges.add(frozenset({loop[i], loop[(i + 1) % len(loop)]}))

    def complex(self):
        C = set(self.tris) | set(self.edges)
        for c in list(C):
            for v in c:
                C.add(frozenset({v}))
        return C


def cylinder(a, b):
    """Annulus between 3-cycles a,b (vertex triples): 6 triangles, boundary a+b."""
    m = len(a)
    return ([(a[i], a[(i + 1) % m], b[i]) for i in range(m)]
            + [(a[(i + 1) % m], b[i], b[(i + 1) % m]) for i in range(m)])


def disk(a, ctr):
    """Cap the 3-cycle a with center vertex ctr: 3 triangles, boundary a."""
    return [(ctr, a[i], a[(i + 1) % len(a)]) for i in range(len(a))]


def pants(a, b, c):
    """Pair of pants with boundary a+b+c: cylinder a~b, one triangle punched out, hole tubed to c."""
    cyl = cylinder(a, b)
    hole = (a[0], a[1], b[0])
    cyl = [t for t in cyl if set(t) != set(hole)]
    return cyl + cylinder([a[0], a[1], b[0]], c)
# ---- end of inlined helpers ----

# ---- inlined from newclaims.py ----
def submatrix_rank(A, R, C):
    rows = [[A[i][j] for j in sorted(C)] for i in sorted(R)]
    if not rows or not rows[0]:
        return 0
    return matrix_rank(rows)


def build_tube_switched(A, r, k, act_rows, act_cols):
    b = Builder()
    # row i: copies C[i][j] for j in range(k), consecutive copies joined by annuli (fresh vertices)
    C = [[b.fresh(3) for _ in range(k)] for _ in range(r)]
    for i in range(r):
        for j in range(k):
            b.add_loop(C[i][j])
        for j in range(k - 1):
            b.add_tris(cylinder(C[i][j], C[i][j + 1]))
    switch_tris = []
    apex_row = []
    for i in range(r):
        x = b.fresh(1)[0]
        apex_row.append(x)
        # cone vertex + edges always present (pre-allocated); triangles toggled
        for v in C[i][0]:
            b.edges.add(frozenset({x, v}))
        if i not in act_rows:
            b.add_tris(disk(C[i][0], x))
    for j in range(k):
        P = b.fresh(3); b.add_loop(P)
        s_prev = b.fresh(3); b.add_loop(s_prev)
        b.add_tris(disk(s_prev, b.fresh(1)[0]))
        s_mid = b.fresh(3); b.add_loop(s_mid)
        b.add_tris(pants(s_prev, P, s_mid))
        s_prev = s_mid
        for i in range(r):
            s_next = b.fresh(3); b.add_loop(s_next)
            if A[i][j] == 1:
                b.add_tris(pants(s_prev, C[i][j], s_next))
            else:
                b.add_tris(cylinder(s_prev, s_next))
            s_prev = s_next
        b.add_tris(disk(s_prev, b.fresh(1)[0]))
        y = b.fresh(1)[0]
        for v in P:
            b.edges.add(frozenset({y, v}))
        if j in act_cols:
            b.add_tris(disk(P, y))
    return b


def complex_of(b):
    Cx = set(b.tris) | set(b.edges)
    for c in list(Cx):
        for v in c:
            Cx.add(frozenset({v}))
    return Cx


def max_degree(Cx):
    deg = {}
    for c in Cx:
        if len(c) == 2:
            for v in c:
                deg[v] = deg.get(v, 0) + 1
    return max(deg.values()) if deg else 0
# ---- end ----

def comparability_graph(K):
    K = list(K)
    adj = {s: set() for s in K}
    by = {}
    for s in K:
        by.setdefault(len(s), []).append(s)
    for s in K:
        for k in range(1, len(s)):
            for f in combinations(sorted(s), k):
                f = frozenset(f)
                adj[s].add(f); adj[f].add(s)
    return adj

def clique_complex(adj, maxdim=3):
    V = list(adj)
    idx = {v: i for i, v in enumerate(V)}
    out = set(frozenset({idx[v]}) for v in V)
    # enumerate cliques up to size maxdim+1 by extension
    frontier = [frozenset({idx[v]}) for v in V]
    nbr = {idx[v]: {idx[w] for w in adj[v]} for v in V}
    for size in range(2, maxdim + 2):
        nxt = []
        for c in frontier:
            m = max(c)
            common = set.intersection(*[nbr[x] for x in c])
            for w in common:
                if w > m:
                    nc = c | {w}
                    nxt.append(nc); out.add(nc)
        frontier = nxt
    return out

def sd(K):
    # order complex of face poset: chains
    K = list(K)
    idx = {s: i for i, s in enumerate(K)}
    out = set()
    def extend(chain):
        out.add(frozenset(idx[s] for s in chain))
        top = chain[-1]
        for s in K:
            if top < s:
                extend(chain + [s])
    for s in K:
        extend([s])
    return out

def random_complex(rng, nv, pe, pt):
    V = [frozenset({v}) for v in range(nv)]
    E = [frozenset(e) for e in combinations(range(nv), 2) if rng.random() < pe]
    Es = set(E)
    T = [frozenset(t) for t in combinations(range(nv), 3)
         if all(frozenset(e) in Es for e in combinations(t, 2)) and rng.random() < pt]
    return set(V + E + T)

def check_sd(trials=20):
    rng = random.Random(31)
    ok = tot = 0
    for _ in range(trials):
        U = random_complex(rng, rng.randint(4, 7), 0.7, 0.6)
        # random subcomplex K of U: random simplices + closure
        pick = [s for s in U if rng.random() < 0.5]
        K = set()
        for s in pick:
            for k in range(1, len(s) + 1):
                for f in combinations(sorted(s), k):
                    K.add(frozenset(f))
        GU = comparability_graph(U)
        induced = {s: {t for t in GU[s] if t in K} for s in K}
        cl = clique_complex(induced, maxdim=3)
        sdK = sd(K)
        same = (len(cl) == len(sdK)) and (sorted(map(len, cl)) == sorted(map(len, sdK)))
        bK = betti(K)[:3]; bC = betti(cl)[:3]
        tot += 1; ok += same and bK == bC
    print(f"(a,b) clique complex of induced comparability subgraph == sd(K) (sizes) and Betti(K) == Betti(Cl): {ok}/{tot}")
    return ok == tot

def check_degree():
    rng = random.Random(3)
    degs = []
    for (r, k) in [(3, 3), (4, 6), (5, 8)]:
        A = [[1] * k for _ in range(r)]
        b = build_tube_switched(A, r, k, set(range(r)), set(range(k)))
        U = complex_of(b)
        # universe includes all switch triangles: add both states
        b2 = build_tube_switched(A, r, k, set(), set())
        U2 = complex_of(b2)
        # vertex ids coincide across builds (same fresh() order), so union is the universe
        U = U | U2
        G = comparability_graph(U)
        d = max(len(v) for v in G.values())
        degs.append(d)
        print(f"   tube universe {r}x{k} all-ones: |U| = {len(U)}, max degree of G_U = {d}")
    return degs

if __name__ == '__main__':
    r = check_sd()
    degs = check_degree()
    bounded = len(set(degs)) == 1 and degs[0] <= 25
    print(f'(c) maximum degree of the comparability graph is the same constant for all sizes: {bounded}')
    print('ALL VALIDATED:', r and bounded)
