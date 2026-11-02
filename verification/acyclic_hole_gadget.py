"""Re-verification of the acyclicity construction on the integrator's HOLE gadget (Def. def:gadget), LEAN version.
Socket between a=s_t and b=s_{t+1}: Cyl(a,b) minus h=(a0,a1,b0); sealed (h) if A_ij=0, tubed Cyl(h, C_i) if A_ij=1.
Column j: s_0..s_{d+1}, cones on s_0 and s_{d+1}, first socket (s_0,s_1) tubed to tether P_j, tether filled (column active).
Lean complex: all triangles + their faces + row cycles (and nothing else).  Spine: base vertices s_t[0], C_i[0];
edges s_t[0]s_{t+1}[0] (in every socket) and attachment edges h_0 c_0 = s_t[0] C_i[0] (in tubes).  Cone apex z.
Checks: (a) (beta0,beta1,beta2) = (1, r-rank, k-rank); (b) bordered: beta = (1,1-par,1-par);
(c) flip cost in simplices; (d) all spine edges are present in the lean complex.
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

def cyl(a, b):
    return [(a[t], a[(t+1)%3], b[t]) for t in range(3)] + [(a[(t+1)%3], b[t], b[(t+1)%3]) for t in range(3)]

def cone(a, o):
    return [(o, a[t], a[(t+1)%3]) for t in range(3)]

class B:
    def __init__(s): s.V = 0; s.T = set(); s.E = set()
    def fresh(s, n):
        x = list(range(s.V, s.V+n)); s.V += n; return x
    def tris(s, ts):
        for t in ts:
            t = frozenset(t); assert len(t) == 3; s.T.add(t)
            for e in combinations(sorted(t), 2): s.E.add(frozenset(e))
    def loop(s, a):
        for t in range(3): s.E.add(frozenset({a[t], a[(t+1)%3]}))
    def complex(s):
        C = set(s.T) | set(s.E)
        for c in list(C):
            for v in c: C.add(frozenset({v}))
        return C

def socket(b, a, c_next, target):
    """socket between a and c_next; target None => sealed; else tubed to target."""
    h = (a[0], a[1], c_next[0])
    tr = [t for t in cyl(a, c_next) if frozenset(t) != frozenset(h)]
    b.tris(tr)
    if target is None:
        b.tris([h])
    else:
        b.tris(cyl(list(h), target))

def build(A, r, k, coned=True):
    b = B()
    C = [b.fresh(3) for _ in range(r)]
    for c in C: b.loop(c)                      # row cycles always present (lean: only these extra edges)
    spine_E = set(); spine_V = set(c[0] for c in C)
    for j in range(k):
        P = b.fresh(3)
        s = [b.fresh(3) for _ in range(r + 2)]
        b.tris(cone(s[0], b.fresh(1)[0]))
        socket(b, s[0], s[1], P)               # tether tube
        b.tris([tuple(P)])                     # tether filled (column active)
        spine_E.add(frozenset({s[0][0], s[1][0]}))
        for t in range(1, r + 1):
            i = t - 1
            socket(b, s[t], s[t+1], C[i] if A[i][j] else None)
            spine_E.add(frozenset({s[t][0], s[t+1][0]}))
            if A[i][j]:
                spine_E.add(frozenset({s[t][0], C[i][0]}))
        b.tris(cone(s[r+1], b.fresh(1)[0]))
        for x in s: spine_V.add(x[0])
    for e in spine_E:
        assert e in b.E, ("spine edge missing", e)
    if coned:
        z = b.fresh(1)[0]
        for v in spine_V: b.E.add(frozenset({z, v}))
        for e in spine_E: b.tris([tuple(e) + (z,)])
    return b.complex()

def bordered(M, u, v):
    l = len(M); n = 2*l + 1
    A = [[0]*n for _ in range(n)]
    for i in range(l):
        A[i][i] = 1; A[l+i][l+i] = 1
        for j in range(l): A[i][l+j] = M[i][j]
    for i in range(l): A[2*l][i] = u[i]
    for j in range(l): A[l+j][2*l] = v[j]
    return A, n

if __name__ == '__main__':
    rng = random.Random(41)
    ok = tot = 0
    for _ in range(30):
        r = rng.randint(1, 4); k = rng.randint(1, 4)
        A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
        b0, b1, b2, _ = betti(build(A, r, k))
        rk = matrix_rank(A)
        tot += 1; ok += (b0, b1, b2) == (1, r - rk, k - rk)
    print(f"(a) hole gadget, lean, coned: (beta0,beta1,beta2) = (1, r-rank, k-rank): {ok}/{tot}")
    ok2 = tot2 = 0; worst = 0; dims = set()
    for _ in range(20):
        l = rng.randint(1, 3)
        M = [[rng.randint(0, 1) for _ in range(l)] for _ in range(l)]
        u = [rng.randint(0, 1) for _ in range(l)]; v = [rng.randint(0, 1) for _ in range(l)]
        A, n = bordered(M, u, v)
        par = sum(u[i]*M[i][j]*v[j] for i in range(l) for j in range(l)) % 2
        K1 = build(A, n, n)
        b0, b1, b2, _ = betti(K1)
        tot2 += 1; ok2 += (b0, b1, b2) == (1, 1 - par, 1 - par)
        u2 = u[:]; i = rng.randrange(l); u2[i] ^= 1
        A2, _ = bordered(M, u2, v)
        d = K1 ^ build(A2, n, n)
        worst = max(worst, len(d)); dims |= {len(c) for c in d}
    print(f"(b) bordered: beta = (1, 1-par, 1-par): {ok2}/{tot2}")
    print(f"(c) border flip = {worst} simplex updates, simplex sizes involved {sorted(dims)} (2=edges, 3=triangles)")
    print('ALL VALIDATED:', ok == tot and ok2 == tot2 and worst == 14)
