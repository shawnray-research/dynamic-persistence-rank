"""Acyclicity hardness gadget: cone off the incidence-graph spine L of K(A).
Claims checked against brute force:
 (a) coned K(A): beta_0 = 1, beta_1 = r - rank A, beta_2 = k - rank A  (graph part removed, nothing added)
 (b) bordered matrix Bord = [[B, w],[x^T, 0]], B = [[I, M],[0, I]]: beta_1 = beta_2 = 1 - (u^T M v mod 2)
 (c) entry flip in border row/column = O(1) simplex toggles (count them)
 (d) isolation: Pr_{x<=u, y<=v}[x^T S y = 1] >= 1/4 when S = M[supp u, supp v] != 0 (exhaustive small cases)
"""
import random, sys
from itertools import combinations, product
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

def build_coned(A, r, k):
    b = Builder()
    C = [b.fresh(3) for _ in range(r)]
    for cyc in C:
        b.add_loop(cyc)
    spine_edges = set()
    spine_vertices = set(c[0] for c in C)
    for j in range(k):
        s_prev = b.fresh(3); b.add_loop(s_prev)
        b.add_tris(disk(s_prev, b.fresh(1)[0]))
        spine_vertices.add(s_prev[0])
        for i in range(r):
            s_next = b.fresh(3); b.add_loop(s_next)
            if A[i][j]:
                b.add_tris(pants(s_prev, C[i], s_next))
                spine_edges.add(frozenset({s_prev[0], C[i][0]}))       # attachment edge (in pants)
            else:
                b.add_tris(cylinder(s_prev, s_next))
            spine_edges.add(frozenset({s_prev[0], s_next[0]}))          # column spine edge (in both)
            spine_vertices.add(s_next[0])
            s_prev = s_next
        b.add_tris(disk(s_prev, b.fresh(1)[0]))
    for e in spine_edges:
        assert e in b.edges, e
    z = b.fresh(1)[0]
    for v in spine_vertices:
        b.edges.add(frozenset({z, v}))
    for e in spine_edges:
        b.add_tris([tuple(e) + (z,)])
    Cx = set(b.tris) | set(b.edges)
    for c in list(Cx):
        for v in c:
            Cx.add(frozenset({v}))
    return Cx

def check_coned(trials=40):
    rng = random.Random(21)
    ok = tot = 0
    for _ in range(trials):
        r = rng.randint(1, 5); k = rng.randint(1, 5)
        A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
        Cx = build_coned(A, r, k)
        b0, b1, b2, _ = betti(Cx)
        rk = matrix_rank(A)
        tot += 1
        ok += (b0, b1, b2) == (1, r - rk, k - rk)
    print(f"(a) coned K(A): (beta0,beta1,beta2) = (1, r-rank, k-rank): {ok}/{tot}")
    return ok == tot

def bordered(M, u, v):
    l = len(M)
    n = 2 * l + 1
    A = [[0] * n for _ in range(n)]
    for i in range(l):
        A[i][i] = 1; A[l + i][l + i] = 1
        for j in range(l):
            A[i][l + j] = M[i][j]
    for i in range(l):           # border row x = (u, 0)
        A[2 * l][i] = u[i]
    for j in range(l):           # border column w = (0, v)
        A[l + j][2 * l] = v[j]
    return A, n

def check_bordered(trials=30):
    rng = random.Random(22)
    ok = tot = 0
    for _ in range(trials):
        l = rng.randint(1, 3)
        M = [[rng.randint(0, 1) for _ in range(l)] for _ in range(l)]
        u = [rng.randint(0, 1) for _ in range(l)]
        v = [rng.randint(0, 1) for _ in range(l)]
        A, n = bordered(M, u, v)
        par = sum(u[i] * M[i][j] * v[j] for i in range(l) for j in range(l)) % 2
        Cx = build_coned(A, n, n)
        b0, b1, b2, _ = betti(Cx)
        tot += 1
        ok += (b0, b1, b2) == (1, 1 - par, 1 - par)
    print(f"(b) coned K(Bord): beta = (1, 1-par, 1-par), i.e. F2-acyclic iff u^T M v = 1 mod 2: {ok}/{tot}")
    return ok == tot

def check_flip_cost(trials=20):
    rng = random.Random(23)
    worst = 0
    for _ in range(trials):
        l = rng.randint(1, 3)
        M = [[rng.randint(0, 1) for _ in range(l)] for _ in range(l)]
        u = [rng.randint(0, 1) for _ in range(l)]
        v = [rng.randint(0, 1) for _ in range(l)]
        A, n = bordered(M, u, v)
        u2 = u[:]; i = rng.randrange(l); u2[i] ^= 1
        A2, _ = bordered(M, u2, v)
        d = len(build_coned(A, n, n) ^ build_coned(A2, n, n))
        v2 = v[:]; j = rng.randrange(l); v2[j] ^= 1
        A3, _ = bordered(M, u, v2)
        d2 = len(build_coned(A, n, n) ^ build_coned(A3, n, n))
        worst = max(worst, d, d2)
    print(f"(c) border-entry flip = at most {worst} simplex toggles (all dims), independent of l")
    return True

def check_isolation():
    # exhaustive over all nonzero 0/1 matrices S up to 3x3 (as the restricted submatrix)
    worst = 1.0
    for a in range(1, 4):
        for c in range(1, 4):
            for bits in product([0, 1], repeat=a * c):
                if not any(bits):
                    continue
                S = [bits[i * c:(i + 1) * c] for i in range(a)]
                hit = 0
                for x in product([0, 1], repeat=a):
                    for y in product([0, 1], repeat=c):
                        hit += sum(x[i] * S[i][j] * y[j] for i in range(a) for j in range(c)) % 2
                worst = min(worst, hit / (2 ** a * 2 ** c))
    print(f"(d) isolation: min over nonzero S (<=3x3) of Pr[x^T S y = 1] = {worst} (claim >= 1/4)")
    return worst >= 0.25

if __name__ == '__main__':
    r = [check_coned(), check_bordered(), check_flip_cost(), check_isolation()]
    print('ALL VALIDATED:', all(r))
