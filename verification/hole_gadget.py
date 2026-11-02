"""hole_gadget.py -- the 7-toggle 'hole' socket: each socket is cylinder(s_{i-1}, s_i) minus the hole triangle
h=(a0,a1,c0); A_ij=0 -> hole sealed by h (1 triangle); A_ij=1 -> 6-triangle tube from h's boundary to row cycle C_i.
Checks: beta_2 = dim Z_2 = k - rank A (F2, brute force), switched identity, flip = 7 triangle toggles,
chi = 2k - nnz, beta_1 formula nnz - k - rk + c(G_A)."""
import random

# ---- self-contained F2 homology helpers (copied from the repository's dynrank.py) ----
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
    lower = [c for c in cells if len(c) == p]
    upper = [c for c in cells if len(c) == p + 1]
    idx = {c: i for i, c in enumerate(lower)}
    cols = [{idx[frozenset(c - {v})] for v in c if frozenset(c - {v}) in idx} for c in upper]
    return f2_rank(cols)


def betti(cells):
    n = [len([c for c in cells if len(c) == d + 1]) for d in range(4)]
    r = [boundary_rank(cells, d + 1) for d in range(4)]
    return (n[0] - r[0], (n[1] - r[0]) - r[1], (n[2] - r[1]) - r[2], (n[3] - r[2]) - r[3])


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
    """Annulus between triangle cycles a, b: 6 triangles, boundary a + b."""
    m = len(a)
    return ([(a[i], a[(i + 1) % m], b[i]) for i in range(m)]
            + [(a[(i + 1) % m], b[i], b[(i + 1) % m]) for i in range(m)])


def disk(a, ctr):
    """Cone on the triangle cycle a with apex ctr: 3 triangles, boundary a."""
    return [(ctr, a[i], a[(i + 1) % len(a)]) for i in range(len(a))]

def socket(s_prev, s_next, C, bit):
    cyl = cylinder(s_prev, s_next)
    h = (s_prev[0], s_prev[1], s_next[0])
    assert any(set(t) == set(h) for t in cyl)
    base = [t for t in cyl if set(t) != set(h)]
    return base + ([h] if bit == 0 else cylinder(list(h), C))

def build(A, r, k, act_rows=None, act_cols=None, switched=False):
    b = Builder()
    C = [b.fresh(3) for _ in range(r)]
    for c in C: b.add_loop(c)
    if switched:
        for i in range(r):
            if i not in act_rows: b.add_tris([tuple(C[i])])          # kill switch: fill C_i (1 triangle)
    for j in range(k):
        s_prev = b.fresh(3); b.add_loop(s_prev); b.add_tris(disk(s_prev, b.fresh(1)[0]))
        if switched:
            P = b.fresh(3); b.add_loop(P)
            s_mid = b.fresh(3); b.add_loop(s_mid)
            b.add_tris(socket(s_prev, s_mid, P, 1)); s_prev = s_mid    # tether hole tubed to private P_j
            if j in act_cols: b.add_tris([tuple(P)])                    # activation: fill P_j (1 triangle)
        for i in range(r):
            s_next = b.fresh(3); b.add_loop(s_next)
            b.add_tris(socket(s_prev, s_next, C[i], A[i][j])); s_prev = s_next
        b.add_tris(disk(s_prev, b.fresh(1)[0]))
    return b

def comps(A, r, k):
    par = list(range(r + k))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for i in range(r):
        for j in range(k):
            if A[i][j]: par[f(i)] = f(r + j)
    return len({f(x) for x in range(r + k)})

rng = random.Random(5); ok = tot = 0; flips_ok = 0; sw_ok = 0
for trial in range(60):
    r, k = rng.randint(1, 5), rng.randint(1, 5)
    A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
    b = build(A, r, k); K = b.complex()
    T = len(b.tris); z2 = T - boundary_rank(K, 2); rk = matrix_rank(A); nnz = sum(map(sum, A))
    b0, b1, b2, _ = betti(K)
    V = len([c for c in K if len(c) == 1]); E = len([c for c in K if len(c) == 2])
    chi = V - E + T
    tot += 1
    ok += (z2 == k - rk == b2) and (chi == 2 * k - nnz) and (b0 == comps(A, r, k)) and (b1 == nnz - k - rk + comps(A, r, k))
    i, j = rng.randrange(r), rng.randrange(k)
    A2 = [row[:] for row in A]; A2[i][j] ^= 1
    t1 = set(build(A, r, k).tris); t2 = set(build(A2, r, k).tris)
    flips_ok += (len(t1 ^ t2) == 7)
    u = {x for x in range(r) if rng.random() < .5}; v = {x for x in range(k) if rng.random() < .5}
    bs = build(A, r, k, u, v, switched=True); Ks = bs.complex()
    z2s = len(bs.tris) - boundary_rank(Ks, 2)
    sub = [[A[x][y] for y in sorted(v)] for x in sorted(u)]
    want = len(v) - (matrix_rank(sub) if sub and sub[0] else 0)
    sw_ok += (z2s == want) and (int(z2s < len(v)) == int(any(A[x][y] for x in u for y in v)))
print(f"crux+chi+beta0+beta1 formulas: {ok}/{tot}; flip = 7 triangle toggles: {flips_ok}/60; switched identity (1-triangle caps): {sw_ok}/60")
print("ALL VALIDATED:", ok == tot and flips_ok == 60 and sw_ok == 60)
