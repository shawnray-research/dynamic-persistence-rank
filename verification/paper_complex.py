"""paper_complex.py -- independent check of Section 3 on the EXACT complex of Definition (The gadget).

Builds U(P) for general admissible sets P, keeps every vertex and edge of U(P) in K(A;R,J) (only triangles toggle),
and checks over F2, F3, F5, F7 with signed boundary matrices:
  * Lemma (Crux):  beta_2(K(A;R,J)) = |J| - rank A[R,J];
  * eq. (b1-from-b2): beta_1 = c_U + beta_2 - n_2(K);
randomly (with edge cases: r=0 or k=0, empty P, empty R or J, zero matrix) and EXHAUSTIVELY for all P, A, R, J with
(r,k) in {(<=2,<=2),(3,1),(1,3)} over F2 and F3; plus the remark on signed entries (reversed tubes).
"""
import random
from itertools import combinations

def cyl(a, b):
    # paper: Cyl(a,b) = { a_t a_{t+1} b_t , a_{t+1} b_t b_{t+1} : t in Z3 }
    # oriented pattern: [a_t,a_{t+1},b_t] and [a_{t+1},b_{t+1},b_t]
    out = []
    for t in range(3):
        out.append((a[t], a[(t+1)%3], b[t]))
    for t in range(3):
        out.append((a[(t+1)%3], b[(t+1)%3], b[t]))
    return out

def cone(a, o, rev=False):
    tr = [(o, a[t], a[(t+1)%3]) for t in range(3)]
    if rev:
        tr = [(x, z, y) for (x, y, z) in tr]
    return tr

class U:
    def __init__(self, r, k, P):
        self.r, self.k, self.P = r, k, set(P)
        self.V = 0
        self.tri_label = {}     # oriented tuple -> label
        self.edges = set()
        self.verts = set()
        self.C = [self.fresh(3) for _ in range(r)]
        self.T = [None]*k       # tethers
        self.cols = {}
        for i in range(r):
            self.add_loop(self.C[i])
            self.add_tri(tuple(self.C[i]), ('D', i))
        for j in range(k):
            rows = sorted(i for (i, jj) in self.P if jj == j)
            d = len(rows)
            s = [self.fresh(3) for _ in range(d + 2)]
            for c in s: self.add_loop(c)
            o0, o1 = self.fresh(1)[0], self.fresh(1)[0]
            self.T[j] = self.fresh(3); self.add_loop(self.T[j])
            self.add_tri(tuple(self.T[j]), ('E', j))
            for t in cone(s[0], o0, rev=True): self.add_tri(t, ('cone', j))
            for t in cone(s[d+1], o1): self.add_tri(t, ('cone', j))
            # tether socket between s0 and s1
            self.socket(j, s[0], s[1], self.T[j], ('tether',), seal=False)
            for t in range(1, d + 1):
                self.socket(j, s[t], s[t+1], self.C[rows[t-1]], ('row', rows[t-1]), seal=True)
        self.edges_all = set(self.edges)
    def fresh(self, n):
        xs = list(range(self.V, self.V + n)); self.V += n
        for x in xs: self.verts.add(x)
        return xs
    def add_loop(self, a):
        for t in range(3): self.edges.add(frozenset((a[t], a[(t+1)%3])))
    def add_tri(self, t, lab):
        assert len(set(t)) == 3
        key = frozenset(t)
        assert all(frozenset(x) != key for x in self.tri_label), ('dup', t, lab)
        self.tri_label[t] = lab
        for e in combinations(t, 2): self.edges.add(frozenset(e))
    def socket(self, j, a, b, c, kind, seal):
        cy = cyl(a, b)
        h = (a[0], a[1], b[0])
        assert cy[0] == h
        for t in cy[1:]: self.add_tri(t, ('pcyl', j, kind))
        if seal: self.add_tri(h, ('seal', j, kind))
        for t in cyl(list(h), c): self.add_tri(t, ('tube', j, kind))

    def K(self, A, R, J):
        """triangles of K(A;R,J) as oriented tuples (pattern orientation)."""
        out = []
        for t, lab in self.tri_label.items():
            if lab[0] == 'D':
                if lab[1] not in R: out.append(t)
            elif lab[0] == 'E':
                if lab[1] in J: out.append(t)
            elif lab[0] in ('cone', 'pcyl'):
                out.append(t)
            elif lab[0] == 'seal':
                _, j, (_, i) = lab
                if A[i][j] == 0: out.append(t)
            elif lab[0] == 'tube':
                _, j, kind = lab
                if kind[0] == 'tether' or A[kind[1]][j] == 1: out.append(t)
        return out

def col_of(lab):
    return lab[1] if lab[0] in ('cone', 'pcyl', 'seal', 'tube') else None

# ---------- linear algebra mod p (sparse) ----------
def rank_mod(cols, p):
    """cols: list of dict row->coef. returns rank over F_p (p prime)."""
    piv = {}
    rk = 0
    for c in cols:
        v = {i: x % p for i, x in c.items() if x % p}
        while v:
            m = max(v)
            if m in piv:
                w = piv[m]
                f = v[m] * pow(w[m], p - 2, p) % p
                for i, x in w.items():
                    y = (v.get(i, 0) - f * x) % p
                    if y: v[i] = y
                    else: v.pop(i, None)
            else:
                piv[m] = v; rk += 1; break
    return rk

def bd_cols(simplices, faces_index):
    """signed boundary columns of oriented simplices (tuples) w.r.t. sorted-face index."""
    cols = []
    for s in simplices:
        col = {}
        for i in range(len(s)):
            f = s[:i] + s[i+1:]
            # orientation sign of f relative to sorted(f)
            srt = tuple(sorted(f))
            sign = perm_sign(f, srt)
            idx = faces_index[srt]
            col[idx] = col.get(idx, 0) + ((-1) ** i) * sign
        cols.append(col)
    return cols

def perm_sign(t, srt):
    perm = [srt.index(x) for x in t]
    s = 1
    for i in range(len(perm)):
        for j in range(i+1, len(perm)):
            if perm[i] > perm[j]: s = -s
    return s

def mat_rank(A, rows, cols, p):
    cs = []
    for j in cols:
        cs.append({i: A[i][j] for i in rows if A[i][j] % p})
    return rank_mod(cs, p)

def bettis(verts, edges, tris, p):
    vi = {(v,): n for n, v in enumerate(sorted(verts))}
    el = sorted(tuple(sorted(e)) for e in edges)
    ei = {e: n for n, e in enumerate(el)}
    r1 = rank_mod(bd_cols(el, vi), p)
    r2 = rank_mod(bd_cols(list(tris), ei), p)
    n0, n1, n2 = len(verts), len(el), len(tris)
    return (n0 - r1, n1 - r1 - r2, n2 - r2), (n0, n1, n2)

# ================= random + edge-case checks =================

def run(u, A, R, J, p):
    tris = u.K(A, R, J)
    (b0, b1, b2), (n0, n1, n2) = bettis(u.verts, u.edges_all, tris, p)
    rk = mat_rank(A, sorted(R), sorted(J), p)
    # c_U = beta0(U^(1)) - n0 + n1
    (g0, g1, _), _ = bettis(u.verts, u.edges_all, [], p)
    cU = g0 - len(u.verts) + len(u.edges_all)
    ok_crux = (b2 == len(J) - rk)
    ok_b1 = (b1 == cU + b2 - n2)
    return ok_crux, ok_b1

rng = random.Random(7)
tot = good = goodb1 = 0
cases = []
# edge cases
cases.append((0, 0, set(), [], set(), set()))
cases.append((2, 0, set(), [[], []], set(), set()))
cases.append((2, 0, set(), [[], []], {0, 1}, set()))
cases.append((0, 2, set(), [], set(), {0, 1}))
cases.append((2, 2, set(), [[0, 0], [0, 0]], {0, 1}, {0, 1}))           # P empty
cases.append((2, 2, {(0,0),(0,1),(1,0),(1,1)}, [[0,0],[0,0]], {0,1}, {0,1}))  # zero matrix
cases.append((2, 2, {(0,0),(0,1),(1,0),(1,1)}, [[1,1],[1,1]], set(), {0,1}))  # R empty
cases.append((2, 2, {(0,0),(0,1),(1,0),(1,1)}, [[1,1],[1,1]], {0,1}, set()))  # J empty
# adversarial sign matrices (rank of |A| vs signed versions differ over F3)
for M in ([[1,1],[1,1]], [[1,1,0],[0,1,1],[1,0,1]], [[1,1,1],[1,1,1],[1,1,1]],
          [[1,0,1,1],[0,1,1,1],[1,1,0,1]], [[1,1,0,0],[0,1,1,0],[0,0,1,1],[1,0,0,1]]):
    r, k = len(M), len(M[0])
    P = {(i, j) for i in range(r) for j in range(k)}
    cases.append((r, k, P, M, set(range(r)), set(range(k))))
for trial in range(250):
    r, k = rng.randint(0, 4), rng.randint(0, 4)
    d = rng.random()
    P = {(i, j) for i in range(r) for j in range(k) if rng.random() < d}
    A = [[(1 if (i, j) in P and rng.random() < 0.6 else 0) for j in range(k)] for i in range(r)]
    R = {i for i in range(r) if rng.random() < 0.6}
    J = {j for j in range(k) if rng.random() < 0.6}
    cases.append((r, k, P, A, R, J))
for (r, k, P, A, R, J) in cases:
    u = U(r, k, P)
    for p in (2, 3, 5, 7):
        c, b = run(u, A, R, J, p)
        tot += 1; good += c; goodb1 += b
        if not (c and b): print('FAIL', r, k, sorted(P), A, R, J, p, c, b)
print(f'crux: {good}/{tot}   eq.(b1-from-b2): {goodb1}/{tot}')

ok_random = (good == tot and goodb1 == tot)

# ================= exhaustive checks =================
from itertools import product
tot = bad = 0
for r, k in [(0,0),(1,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(1,3)]:
    cells = [(i, j) for i in range(r) for j in range(k)]
    for pm in product([0, 1], repeat=len(cells)):
        P = {c for c, b in zip(cells, pm) if b}
        u = U(r, k, P)
        (g0, g1, _), _ = bettis(u.verts, u.edges_all, [], 2)
        cU = g0 - len(u.verts) + len(u.edges_all)
        Pl = sorted(P)
        for am in product([0, 1], repeat=len(Pl)):
            A = [[0] * k for _ in range(r)]
            for (i, j), b in zip(Pl, am): A[i][j] = b
            for rm in product([0, 1], repeat=r):
                R = {i for i in range(r) if rm[i]}
                for jm in product([0, 1], repeat=k):
                    J = {j for j in range(k) if jm[j]}
                    tris = u.K(A, R, J)
                    for p in (2, 3):
                        (b0, b1, b2), (n0, n1, n2) = bettis(u.verts, u.edges_all, tris, p)
                        rk = mat_rank(A, sorted(R), sorted(J), p)
                        tot += 1
                        if b2 != len(J) - rk or b1 != cU + b2 - n2: bad += 1
print('exhaustive (r,k) up to (2,2),(3,1),(1,3); all P, A, R, J; F2 and F3:', tot - bad, '/', tot)

ok_exh = (bad == 0)

# ---------- signed entries {0,+1,-1}: reversed tube Cyl(h, cbar), cbar = (c0, c2, c1) ----------
def signed_complex_tris(r, k, A, R, J):
    """K(A;R,J) for a {0,+-1} matrix with P = all positions: seal if 0, tube to C_i if +1, reversed tube if -1."""
    V = [0]
    def fresh(n):
        xs = list(range(V[0], V[0] + n)); V[0] += n; return xs
    C = [fresh(3) for _ in range(r)]
    tris, edges, verts = [], set(), set(range(0))
    def add(ts):
        for t in ts:
            tris.append(t)
            for e in combinations(t, 2): edges.add(frozenset(e))
    for i in range(r):
        if i not in R: add([tuple(C[i])])
    for j in range(k):
        s = [fresh(3) for _ in range(r + 2)]
        T = fresh(3); o0, o1 = fresh(1)[0], fresh(1)[0]
        for c in s + [T] + C:
            for t in range(3): edges.add(frozenset((c[t], c[(t+1)%3])))
        if j in J: add([tuple(T)])
        add(cone(s[0], o0, rev=True)); add(cone(s[r+1], o1))
        def sock(a, b, c, val):
            cy = cyl(a, b); h = (a[0], a[1], b[0]); add(cy[1:])
            if val == 0: add([h])
            elif val == 1: add(cyl(list(h), c))
            else: add(cyl(list(h), [c[0], c[2], c[1]]))
        sock(s[0], s[1], T, 1)
        for t in range(1, r + 1): sock(s[t], s[t+1], C[t-1], A[t-1][j])
    verts = set(v for e in edges for v in e)
    return verts, edges, tris

def signed_check():
    rng = random.Random(13); ok = tot = 0
    for trial in range(120):
        r, k = rng.randint(1, 4), rng.randint(1, 4)
        A = [[rng.choice((-1, 0, 1)) for _ in range(k)] for _ in range(r)]
        R = {i for i in range(r) if rng.random() < 0.7}; J = {j for j in range(k) if rng.random() < 0.7}
        verts, edges, tris = signed_complex_tris(r, k, A, R, J)
        for p in (3, 5, 7):
            (b0, b1, b2), _ = bettis(verts, edges, tris, p)
            tot += 1; ok += (b2 == len(J) - mat_rank(A, sorted(R), sorted(J), p))
    print(f"signed entries {{0,+1,-1}} with reversed tubes, over F3/F5/F7: {ok}/{tot}")
    return ok == tot

ok_signed = signed_check()
print('ALL VALIDATED:', ok_random and ok_exh and ok_signed)
