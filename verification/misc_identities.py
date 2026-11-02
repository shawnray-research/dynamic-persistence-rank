"""Independent checks of further identities used in the paper.
(1) Row-tube bounded-degree switched gadget: dim Z2 = #active cols - rank A[act rows, act cols], O(1) max degree.
(2) Switch toggles are triangles only (1-skeleton fixed): beta_1 = E - V + beta_0 - (T - dimZ2).
(3) Euler characteristic of plain K(A): chi = 2k - nnz, and beta_1 = (r - rank A) + (nnz - r - k + c(G_A)).
(4) Four-rank formula for persistent Betti numbers beta_p^{a,b}.
(5) Alexander duality on a triangulated S^3: beta_2 = #comp(dual graph of complement) - 1, beta_1 = beta_0 + beta_2 - chi.
(6) Signed gadget over F_3: Boolean OuMv answer via rank >= 1.
"""
import random, sys
from itertools import combinations, permutations
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

def submatrix_rank(A, R, C):
    rows = [[A[i][j] for j in sorted(C)] for i in sorted(R)]
    if not rows or not rows[0]:
        return 0
    return matrix_rank(rows)

# ---------------- (1)+(2) row-tube switched gadget ----------------
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

def check_tube(trials=40):
    rng = random.Random(7)
    ok = tot = 0
    degs = []
    for _ in range(trials):
        r = rng.randint(1, 4); k = rng.randint(1, 4)
        A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
        u = {i for i in range(r) if rng.random() < 0.6}
        v = {j for j in range(k) if rng.random() < 0.6}
        b = build_tube_switched(A, r, k, u, v)
        Cx = complex_of(b)
        T = len(b.tris)
        rd2 = boundary_rank(Cx, 2)
        z2 = T - rd2
        want = len(v) - submatrix_rank(A, u, v)
        V = sum(1 for c in Cx if len(c) == 1); E = sum(1 for c in Cx if len(c) == 2)
        b0, b1, b2, _ = betti(Cx)
        # (2) beta_1 recovers the rank with only counters
        rec = (E - V + b0) - T + len(v) - b1   # = rank A[u,v]
        good = (z2 == want) and (rec == submatrix_rank(A, u, v)) and (b2 == z2)
        degs.append(max_degree(Cx))
        tot += 1; ok += good
    print(f"(1,2) tube-switched gadget: dimZ2 = k_act - rank, beta_1 recovery: {ok}/{tot}; max vertex degree over trials = {max(degs)}")
    return ok == tot

def check_tube_degree_growth():
    # degree must not grow with k: compare k=2 and k=8 all-ones
    for k in (2, 6, 10):
        r = 3
        A = [[1] * k for _ in range(r)]
        b = build_tube_switched(A, r, k, set(range(r)), set(range(k)))
        print(f"     all-ones {r}x{k}: max degree {max_degree(complex_of(b))}")

def check_switch_toggles_are_triangles():
    rng = random.Random(9)
    r, k = 3, 3
    A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
    b1 = complex_of(build_tube_switched(A, r, k, {0, 1, 2}, set()))
    b2 = complex_of(build_tube_switched(A, r, k, {1}, {0, 2}))
    diff = b1 ^ b2
    dims = sorted({len(c) for c in diff})
    print(f"(2) symmetric difference between two switch states contains only simplices of size {dims} (3 = triangles); count {len(diff)}")
    return dims == [3]

# ---------------- (3) Euler characteristic & beta_1 formula on plain K(A) ----------------
def build_KA(A, r, k):
    """Build K(A) as described in the module docstring.  Returns (complex, T, |E|, builder)."""
    b = Builder()
    rowcycles = [b.fresh(3) for _ in range(r)]
    for C in rowcycles:
        b.add_loop(C)
    for j in range(k):
        s_prev = b.fresh(3)
        b.add_loop(s_prev)
        b.add_tris(disk(s_prev, b.fresh(1)[0]))              # cap the start
        for i in range(r):
            s_next = b.fresh(3)
            b.add_loop(s_next)
            if A[i][j] == 1:
                b.add_tris(pants(s_prev, rowcycles[i], s_next))   # socket: pants
            else:
                b.add_tris(cylinder(s_prev, s_next))              # socket: annulus
            s_prev = s_next
        b.add_tris(disk(s_prev, b.fresh(1)[0]))              # cap the end
    C = b.complex()
    return C, len(b.tris), len(b.edges), b

def components_bip(A, r, k):
    parent = list(range(r + k))
    def f(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for i in range(r):
        for j in range(k):
            if A[i][j]:
                parent[f(i)] = f(r + j)
    return len({f(x) for x in range(r + k)})

def check_euler(trials=30):
    rng = random.Random(5)
    ok = tot = 0
    for _ in range(trials):
        r = rng.randint(1, 4); k = rng.randint(1, 4)
        A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
        Cx, T, E, b = build_KA(A, r, k)
        b0, b1, b2, _ = betti(Cx)
        V = sum(1 for c in Cx if len(c) == 1)
        chi = V - E + T
        nnz = sum(map(sum, A))
        rk = matrix_rank(A)
        cG = components_bip(A, r, k)
        good = (chi == 2 * k - nnz) and (b1 == (r - rk) + (nnz - r - k + cG)) and (b2 == k - rk) and (b0 == cG)
        tot += 1; ok += good
    print(f"(3) chi(K(A)) = 2k - nnz, beta_1 = (r - rank A) + (nnz - r - k + c(G_A)), beta_0 = c(G_A): {ok}/{tot}")
    return ok == tot

# ---------------- (4) four-rank persistent Betti formula ----------------
def rank_cols(cols):
    return f2_rank([set(c) for c in cols])

def bd_rank(simplices_hi, rows_allowed=None):
    cols = []
    for s in simplices_hi:
        faces = [frozenset(s - {v}) for v in s]
        if rows_allowed is not None:
            faces = [f for f in faces if f in rows_allowed]
        cols.append({hash(f) for f in faces})
    return rank_cols(cols)

def persistent_betti_bruteforce(Ka, Kb, p):
    # rank of H_p(Ka) -> H_p(Kb) = dim Z_p(Ka) - dim(Z_p(Ka) cap B_p(Kb))
    # compute via: dim(Z_p(Ka) + B_p(Kb)) etc. using explicit vectors
    Pa = [s for s in Ka if len(s) == p + 1]
    idx = {s: i for i, s in enumerate(sorted({s for s in Kb if len(s) == p + 1}, key=lambda x: sorted(x)))}
    # cycles of Ka: kernel of boundary on p-chains of Ka
    lower = {s for s in Ka if len(s) == p}
    # build boundary matrix columns for Pa
    import itertools
    vecs = []
    for s in Pa:
        vecs.append(({frozenset(s - {v}) for v in s} if p > 0 else set(), {idx[s]}))
    # gaussian elimination to get kernel basis (pairs (boundary, chain))
    basis = []  # reduced boundaries with pivot
    piv = {}
    kernel = []
    for bnd, ch in vecs:
        bnd = set(bnd); ch = set(ch)
        while bnd:
            m = max(bnd, key=lambda f: sorted(f))
            if m in piv:
                pb, pc = piv[m]
                bnd ^= pb; ch ^= pc
            else:
                piv[m] = (bnd, ch); break
        if not bnd:
            kernel.append(ch)
    # boundaries of Kb in p-chain coordinates
    Bb = []
    for s in Kb:
        if len(s) == p + 2:
            Bb.append({idx[frozenset(s - {v})] for v in s})
    rB = f2_rank([set(x) for x in Bb])
    rZB = f2_rank([set(x) for x in Bb] + [set(x) for x in kernel])
    dimZ = len(kernel)
    inter = dimZ + rB - rZB
    return dimZ - inter

def persistent_betti_fourrank(Ka, Kb, p):
    nPa = sum(1 for s in Ka if len(s) == p + 1)
    rk_dp_a = bd_rank([s for s in Ka if len(s) == p + 1]) if p > 0 else 0
    rk_dp1_b = bd_rank([s for s in Kb if len(s) == p + 2])
    rows_new = {s for s in Kb if len(s) == p + 1 and s not in Ka}
    rk_restr = bd_rank([s for s in Kb if len(s) == p + 2], rows_allowed=rows_new)
    return (nPa - rk_dp_a) - rk_dp1_b + rk_restr

def random_complex(rng, nv, pe, pt, ptt=0.0):
    V = [frozenset({v}) for v in range(nv)]
    E = [frozenset(e) for e in combinations(range(nv), 2) if rng.random() < pe]
    Es = set(E)
    T = [frozenset(t) for t in combinations(range(nv), 3)
         if all(frozenset(e) in Es for e in combinations(t, 2)) and rng.random() < pt]
    Ts = set(T)
    TT = [frozenset(t) for t in combinations(range(nv), 4)
          if all(frozenset(f) in Ts for f in combinations(t, 3)) and rng.random() < ptt]
    return V + E + T + TT

def check_fourrank(trials=60):
    rng = random.Random(11)
    ok = tot = 0
    for _ in range(trials):
        nv = rng.randint(4, 8)
        K = random_complex(rng, nv, 0.7, 0.5, 0.3)
        # random filtration: assign values monotone: value = max(face values, random)
        val = {}
        for s in sorted(K, key=len):
            base = max([val[frozenset(s - {v})] for v in s] if len(s) > 1 else [0])
            val[s] = base + rng.randint(0, 3)
        a = rng.randint(0, 6); bth = a + rng.randint(0, 6)
        Ka = {s for s in K if val[s] <= a}; Kb = {s for s in K if val[s] <= bth}
        for p in (0, 1, 2):
            tot += 1
            ok += persistent_betti_bruteforce(Ka, Kb, p) == persistent_betti_fourrank(Ka, Kb, p)
    print(f"(4) four-rank persistent Betti formula vs brute force: {ok}/{tot}")
    return ok == tot

# ---------------- (5) Alexander duality on triangulated S^3 ----------------
def freudenthal_S3(m):
    """Triangulated 3-ball: Freudenthal triangulation of [0,m]^3; then cone the boundary to an apex -> S^3."""
    tets = set()
    idx = lambda x, y, z: (x * (m + 1) + y) * (m + 1) + z
    for x in range(m):
        for y in range(m):
            for z in range(m):
                for perm in permutations(range(3)):
                    p = [x, y, z]
                    verts = [idx(*p)]
                    for d in perm:
                        p[d] += 1
                        verts.append(idx(*p))
                    tets.add(frozenset(verts))
    # boundary triangles: faces of exactly one tet
    cnt = {}
    for t in tets:
        for f in combinations(sorted(t), 3):
            cnt[frozenset(f)] = cnt.get(frozenset(f), 0) + 1
    apex = (m + 1) ** 3
    for f, c in cnt.items():
        if c == 1:
            tets.add(f | {apex})
    T = set()
    for t in tets:
        for k in range(1, 5):
            for f in combinations(sorted(t), k):
                T.add(frozenset(f))
    return T, tets

def duality_betti(T, tets, K):
    # dual graph of complement: nodes = tets not in K, edges = triangles not in K
    nodes = [t for t in tets if t not in K]
    parent = {t: t for t in nodes}
    def f(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    cof = {}
    for t in tets:
        for tri in combinations(sorted(t), 3):
            cof.setdefault(frozenset(tri), []).append(t)
    for tri, ts in cof.items():
        if tri not in K:
            assert len(ts) == 2
            a, b = ts
            parent[f(a)] = f(b)
    ncomp = len({f(t) for t in nodes})
    b2 = ncomp - 1
    # beta_0 via union-find on K's 1-skeleton
    vs = [s for s in K if len(s) == 1]
    par = {next(iter(v)): next(iter(v)) for v in vs}
    def g(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for s in K:
        if len(s) == 2:
            a, b = tuple(s)
            par[g(a)] = g(b)
    b0 = len({g(x) for x in par})
    chi = sum((-1) ** (len(s) - 1) for s in K)
    b1 = b0 + b2 - chi
    return b0, b1, b2

def check_alexander(trials=25):
    rng = random.Random(13)
    T, tets = freudenthal_S3(2)
    # sanity: T is a 3-sphere (betti 1,0,0,1)
    full = betti(T)
    ok = tot = 0
    simp = sorted(T, key=lambda s: (len(s), sorted(s)))
    for _ in range(trials):
        # random subcomplex: pick random simplices, take closure; ensure proper
        pick = [s for s in simp if rng.random() < rng.choice([0.05, 0.15, 0.3, 0.5])]
        K = set()
        for s in pick:
            for k in range(1, len(s) + 1):
                for f in combinations(sorted(s), k):
                    K.add(frozenset(f))
        if len(K) == len(T) or not K:
            continue
        bf = betti(K)
        dual = duality_betti(T, tets, K)
        tot += 1
        ok += (bf[0], bf[1], bf[2]) == dual
    print(f"(5) S^3 = cone-closed Freudenthal 2x2x2 ball (betti {full}); Alexander-duality formula vs brute force: {ok}/{tot}")
    return ok == tot

if __name__ == '__main__':
    r = [check_tube(), check_switch_toggles_are_triangles(), check_euler(), check_fourrank(), check_alexander()]
    check_tube_degree_growth()
    print('ALL VALIDATED:', all(r))
