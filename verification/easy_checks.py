"""easy_checks.py -- computational checks for Section 6 ("Where maintenance is easy").
(1) Lemma lem:dual / Theorem thm:s3 formulas on triangulated 3-spheres (boundary of 4-simplex, cross-polytope,
    random bistellar 1-4 and 2-3 moves), random subcomplexes, over F_2, F_3, F_5 (oriented boundary matrices).
(2) Theorem thm:banded: segment tree with (r_I, W_I) summaries vs. direct rank, random banded matrices, F_2/F_3/F_5.
(3) Corollary cor:bandwidth: width of D_q under min-vertex order <= binom(b+1, q).
(4) Lemma lem:column / Theorem thm:r4: exact rational check that the column model W (built combinatorially exactly as in
    Definition def:gadget) is a geometric simplicial complex in R^3, meets z=0 exactly in the row cycles, and that the
    assembled R^4 complex has injective vertex positions and proper intersections in the binding plane.
Standard library only."""
import random, itertools
from fractions import Fraction as Fr
from math import comb

# ---------------------------------------------------------------- linear algebra over F_p
def rank_mod(rows, p):
    """rows: list of dict col->val. Gaussian elimination over F_p."""
    piv = {}
    rk = 0
    for r in rows:
        r = {c: v % p for c, v in r.items() if v % p}
        while r:
            c = max(r)
            if c in piv:
                pr = piv[c]
                f = r[c] * pow(pr[c], p - 2, p) % p
                for cc, vv in pr.items():
                    nv = (r.get(cc, 0) - f * vv) % p
                    if nv:
                        r[cc] = nv
                    else:
                        r.pop(cc, None)
            else:
                piv[c] = r
                rk += 1
                break
    return rk

def closure(simps):
    C = set()
    for s in simps:
        s = tuple(sorted(s))
        for k in range(1, len(s) + 1):
            for f in itertools.combinations(s, k):
                C.add(f)
    return C

def bd_rank(K, q, p):
    """rank of oriented boundary map C_q -> C_{q-1} of complex K (set of sorted tuples) over F_p."""
    low = sorted(s for s in K if len(s) == q)
    up = [s for s in K if len(s) == q + 1]
    if not low or not up:
        return 0
    idx = {s: i for i, s in enumerate(low)}
    rows = []
    for s in up:
        r = {}
        for a in range(len(s)):
            f = s[:a] + s[a + 1:]
            r[idx[f]] = (-1) ** a
        rows.append(r)
    return rank_mod(rows, p)

def betti(K, p, top=3):
    n = [sum(1 for s in K if len(s) == q + 1) for q in range(top + 2)]
    rk = [0] + [bd_rank(K, q, p) for q in range(1, top + 2)]  # rk[q] = rank d_q (q-simplices -> (q-1)-simplices)
    return [n[q] - rk[q] - rk[q + 1] for q in range(top + 1)]

def ncomp(nodes, edges):
    par = {v: v for v in nodes}
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for u, v in edges:
        a, b = f(u), f(v)
        if a != b:
            par[a] = b
    return len({f(v) for v in nodes})

# ---------------------------------------------------------------- (1) S^3
def s3_triangulations(rng):
    out = []
    out.append([tuple(c) for c in itertools.combinations(range(5), 4)])
    # cross-polytope boundary: vertex 2i = +e_i, 2i+1 = -e_i
    cp = []
    for signs in itertools.product([0, 1], repeat=4):
        cp.append(tuple(sorted(2 * i + signs[i] for i in range(4))))
    out.append(cp)
    for trial in range(4):
        tets = set(tuple(sorted(t)) for t in (cp if trial % 2 else out[0]))
        nv = 8 if trial % 2 else 5
        for move in range(25 + 10 * trial):
            if rng.random() < 0.5:  # 1-4 move
                t = rng.choice(sorted(tets))
                tets.remove(t)
                for f in itertools.combinations(t, 3):
                    tets.add(tuple(sorted(f + (nv,))))
                nv += 1
            else:  # 2-3 move
                tl = sorted(tets)
                rng.shuffle(tl)
                done = False
                edges = closure(tets)
                for t in tl:
                    for f in itertools.combinations(t, 3):
                        others = [u for u in tets if set(f) <= set(u) and u != t]
                        assert len(others) == 1
                        u = others[0]
                        d = (set(t) - set(f)).pop(); e = (set(u) - set(f)).pop()
                        if tuple(sorted((d, e))) in edges:
                            continue
                        tets.remove(t); tets.remove(u)
                        for g in itertools.combinations(f, 2):
                            tets.add(tuple(sorted(g + (d, e))))
                        done = True
                        break
                    if done:
                        break
        out.append(sorted(tets))
    return out

def check_s3(rng):
    tot = ok = 0
    for tets in s3_triangulations(rng):
        T = closure(tets)
        # sanity: (T2) and (T3)
        T3 = [s for s in T if len(s) == 4]
        T2 = [s for s in T if len(s) == 3]
        cof = {t: [s for s in T3 if set(t) <= set(s)] for t in T2}
        assert all(len(v) == 2 for v in cof.values())
        for p in (2, 3):
            assert betti(T, p) == [1, 0, 0, 1], betti(T, p)
        simps = sorted(T, key=lambda s: (len(s), s))
        for trial in range(60):
            # random subcomplex: random subset of simplices, downward closed
            dens = rng.choice([0.05, 0.2, 0.5, 0.8, 0.95])
            pick = [s for s in simps if rng.random() < dens * (0.6 if len(s) == 4 else 1)]
            K = closure(pick)
            if rng.random() < 0.1:
                K = set()
            if K == T:
                continue
            n3 = sum(1 for s in K if len(s) == 4)
            dual_edges = [tuple(cof[t]) for t in T2 if t not in K]
            cG = ncomp(T3, dual_edges)
            V = sorted(s[0] for s in T if len(s) == 1)
            KV = [s[0] for s in K if len(s) == 1]
            KE = [s for s in K if len(s) == 2]
            c0 = ncomp(V, KE)
            b0f = c0 - len(V) + len(KV)
            b2f = cG - n3 - 1
            chi = sum((-1) ** (len(s) - 1) for s in K)
            b1f = b0f + b2f - 0 - chi
            for p in (2, 3, 5):
                b = betti(K, p)
                tot += 1
                ok += (b == [b0f, b1f, b2f, 0])
    return ok, tot

# ---------------------------------------------------------------- (2) banded segment tree
class Banded:
    def __init__(self, M, p):
        self.M, self.p = M, p
        self.r, self.k = len(M), len(M[0])
        self.a = [min(j for j in range(self.k) if M[i][j] % p) for i in range(self.r)]
        self.b = [max(j for j in range(self.k) if M[i][j] % p) for i in range(self.r)]
        self.J = set()
        self.size = 1
        while self.size < self.k:
            self.size *= 2
        # node -> interval [l, h]
        self.iv = {}
        def build(nd, l, h):
            self.iv[nd] = (l, h)
            if l == h:
                return
            m = (l + h) // 2
            build(2 * nd, l, m); build(2 * nd + 1, m + 1, h)
        build(1, 0, self.k - 1)
        self.data = {nd: (0, []) for nd in self.iv}
    def In(self, l, h):
        return {i for i in range(self.r) if l <= self.a[i] and self.b[i] <= h}
    def Bd(self, l, h):
        return {i for i in range(self.r) if not (self.b[i] < l or self.a[i] > h) and not (l <= self.a[i] and self.b[i] <= h)}
    def leaf(self, nd):
        l, h = self.iv[nd]; j = l
        if j not in self.J:
            return (0, [])
        col = {i: self.M[i][j] % self.p for i in range(self.r) if self.M[i][j] % self.p}
        if not col:          # zero column: V = 0 (the paper deletes zero columns in preprocessing)
            return (0, [])
        In = self.In(j, j)
        if any(i in In for i in col):
            return (1, [])
        assert set(col) <= self.Bd(j, j)
        return (0, [col])
    def merge(self, nd):
        l, h = self.iv[nd]
        r1, B1 = self.data[2 * nd]; r2, B2 = self.data[2 * nd + 1]
        l1, h1 = self.iv[2 * nd]; l2, h2 = self.iv[2 * nd + 1]
        X = self.In(l, h) - self.In(l1, h1) - self.In(l2, h2)
        BdI = self.Bd(l, h)
        assert (self.Bd(l1, h1) | self.Bd(l2, h2)) == (BdI | X) and not (BdI & X)
        # echelon with X coordinates first: map coordinate -> priority key (X first)
        order = {i: (0, i) for i in X}
        order.update({i: (1, i) for i in BdI})
        vecs = [dict(v) for v in B1 + B2]
        piv = {}
        for v in vecs:
            v = {c: x % self.p for c, x in v.items() if x % self.p}
            assert set(v) <= set(order)
            while v:
                c = min(v, key=lambda cc: order[cc])
                if c in piv:
                    pv = piv[c]
                    f = v[c] * pow(pv[c], self.p - 2, self.p) % self.p
                    for cc, vv in pv.items():
                        nv = (v.get(cc, 0) - f * vv) % self.p
                        if nv:
                            v[cc] = nv
                        else:
                            v.pop(cc, None)
                else:
                    piv[c] = v
                    break
        nX = sum(1 for c in piv if c in X)
        W = [v for c, v in piv.items() if c not in X]
        assert all(not (set(v) & X) for v in W)
        return (r1 + r2 + nX, W)
    def toggle(self, j):
        self.J ^= {j}
        # find leaf
        nd = 1
        path = []
        while True:
            path.append(nd)
            l, h = self.iv[nd]
            if l == h:
                break
            m = (l + h) // 2
            nd = 2 * nd if j <= m else 2 * nd + 1
        self.data[nd] = self.leaf(nd)
        for a in reversed(path[:-1]):
            self.data[a] = self.merge(a)
    def query(self):
        return self.data[1][0]

def check_banded(rng):
    tot = ok = 0
    for trial in range(80):
        p = rng.choice([2, 3, 5])
        k = rng.randint(2, 14); r = rng.randint(1, 14); bw = rng.randint(0, 4)
        M = []
        for i in range(r):
            a = rng.randrange(k); b = min(k - 1, a + rng.randint(0, bw))
            row = [0] * k
            row[a] = rng.randint(1, p - 1); row[b] = rng.randint(1, p - 1)
            for j in range(a + 1, b):
                if rng.random() < 0.5:
                    row[j] = rng.randrange(p)
            M.append(row)
        D = Banded(M, p)
        w = max(sum(1 for i in range(r) if D.a[i] <= x < D.b[i]) for x in range(k - 1))
        for step in range(40):
            D.toggle(rng.randrange(k))
            cols = sorted(D.J)
            want = rank_mod([{c: M[i][c] for c in cols if M[i][c] % p} for i in range(r)], p)
            tot += 1
            ok += (D.query() == want)
            # bound on stored basis sizes
            assert all(len(Wb) <= 2 * w for _, Wb in D.data.values())
    return ok, tot

# ---------------------------------------------------------------- (3) bandwidth width bound
def check_bandwidth(rng):
    tot = ok = 0
    for trial in range(60):
        n0 = rng.randint(4, 14); b = rng.randint(1, 4)
        # random clique-ish complex with bandwidth b: random simplices inside windows
        simps = []
        for _ in range(rng.randint(3, 25)):
            s = rng.randrange(n0)
            win = list(range(s, min(n0, s + b + 1)))
            kk = rng.randint(1, min(len(win), 4))
            simps.append(tuple(sorted(rng.sample(win, kk))))
        U = closure(simps)
        assert all(max(s) - min(s) <= b for s in U)
        for q in range(1, 4):
            cols = sorted([s for s in U if len(s) == q + 1], key=lambda s: (min(s), s))
            if len(cols) < 2:
                continue
            pos = {s: x for x, s in enumerate(cols)}
            rows = [s for s in U if len(s) == q]
            w = 0
            for x in range(len(cols) - 1):
                cnt = 0
                for rho in rows:
                    ps = [pos[s] for s in cols if set(rho) <= set(s)]
                    if ps and min(ps) <= x < max(ps):
                        cnt += 1
                w = max(w, cnt)
            tot += 1
            ok += (w <= comb(b + 1, q))
    return ok, tot

# ---------------------------------------------------------------- (4) geometry of the column model
def sub(a, b): return tuple(x - y for x, y in zip(a, b))
def add(a, b): return tuple(x + y for x, y in zip(a, b))
def mul(s, a): return tuple(s * x for x in a)
def dot(a, b): return sum(x * y for x, y in zip(a, b))
def cross(a, b): return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])

def proj2(pt, drop):
    return tuple(pt[i] for i in range(3) if i != drop)

def orient2(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

def in_tri2(x, A, B, C):
    o = orient2(A, B, C)
    s = [orient2(A, B, x), orient2(B, C, x), orient2(C, A, x)]
    return all(v * o >= 0 for v in s)

def seg_tri(p, q, A, B, C):
    n = cross(sub(B, A), sub(C, A))
    assert n != (0, 0, 0)
    dp, dq = dot(n, sub(p, A)), dot(n, sub(q, A))
    drop = max(range(3), key=lambda i: abs(n[i]))
    A2, B2, C2 = proj2(A, drop), proj2(B, drop), proj2(C, drop)
    if dp == 0 and dq == 0:
        # coplanar: clip segment p + s (q - p), s in [0,1], by the three edge half-planes
        lo, hi = Fr(0), Fr(1)
        o = orient2(A2, B2, C2)
        p2, q2 = proj2(p, drop), proj2(q, drop)
        for (U, V) in ((A2, B2), (B2, C2), (C2, A2)):
            f0 = orient2(U, V, p2) * o
            f1 = orient2(U, V, q2) * o
            # f(s) = f0 + s (f1 - f0) >= 0
            if f1 == f0:
                if f0 < 0:
                    return []
                continue
            s0 = Fr(-f0, 1) / (f1 - f0)
            if f1 > f0:
                lo = max(lo, s0)
            else:
                hi = min(hi, s0)
        if lo > hi:
            return []
        return [add(p, mul(lo, sub(q, p))), add(p, mul(hi, sub(q, p)))]
    if (dp > 0 and dq > 0) or (dp < 0 and dq < 0):
        return []
    s = Fr(dp) / (dp - dq)
    x = add(p, mul(s, sub(q, p)))
    return [x] if in_tri2(proj2(x, drop), A2, B2, C2) else []

def on_segment(x, a, b):
    d = sub(b, a)
    if cross(sub(x, a), d) != (0, 0, 0):
        return False
    t = dot(sub(x, a), d)
    return 0 <= t <= dot(d, d)

def tri_pair_ok(T1, T2, pos):
    S = set(T1) & set(T2)
    P1 = [pos[v] for v in T1]; P2 = [pos[v] for v in T2]
    pts = []
    for (X, Y) in ((P1, P2), (P2, P1)):
        for a, b in ((0, 1), (1, 2), (2, 0)):
            pts += seg_tri(X[a], X[b], *Y)
    if len(S) == 0:
        return not pts
    if len(S) == 1:
        v = pos[next(iter(S))]
        return all(x == v for x in pts)
    if len(S) == 2:
        a, b = (pos[v] for v in S)
        return all(on_segment(x, a, b) for x in pts)
    return True

def build_universe(r, k, P):
    """Combinatorial U(P) exactly as Definition def:gadget, with vertex positions of Lemma lem:column.
    Returns: dict col -> (list of triangles (vertex-name triples), pos3 dict), row triangles."""
    half = Fr(1, 2)
    delta = [(Fr(0), Fr(1)), (Fr(1), Fr(1)), (half, Fr(2))]
    eta = [(Fr(0), Fr(0)), (Fr(0), Fr(1)), (Fr(1), Fr(0))]
    rowpos = {}
    for i in range(1, r + 1):
        for u in range(3):
            rowpos[('C', i, u)] = (Fr(i) + half * eta[u][0], half * eta[u][1], Fr(0))
    def cyl(a, b):
        return [(a[t], a[(t + 1) % 3], b[t]) for t in range(3)] + [(a[(t + 1) % 3], b[t], b[(t + 1) % 3]) for t in range(3)]
    cols = {}
    for j in range(1, k + 1):
        rows = sorted(i for (i, jj) in P if jj == j)
        d = len(rows)
        pos = dict(rowpos)
        s = [[('s', j, t, u) for u in range(3)] for t in range(d + 2)]
        for t in range(d + 2):
            for u in range(3):
                pos[s[t][u]] = (Fr(t), delta[u][0], delta[u][1])
        Pj = [('P', j, u) for u in range(3)]
        for u in range(3):
            pos[Pj[u]] = (half * eta[u][0], half * eta[u][1], half)
        o1, o2 = ('o', j, 0), ('o', j, 1)
        pos[o1] = (Fr(-1), half, Fr(3, 2)); pos[o2] = (Fr(d + 2), half, Fr(3, 2))
        tris = []
        tris += [(o1, s[0][u], s[0][(u + 1) % 3]) for u in range(3)]
        tris += [(o2, s[d + 1][u], s[d + 1][(u + 1) % 3]) for u in range(3)]
        for t in range(d + 1):
            a, b = s[t], s[t + 1]
            h = (a[0], a[1], b[0])
            C = cyl(a, b)
            assert any(set(x) == set(h) for x in C)
            punct = [x for x in C if set(x) != set(h)]
            tris += punct
            if t == 0:
                tris += cyl(list(h), Pj)               # tether tube (no seal in U(P))
            else:
                i = rows[t - 1]
                tris += [h]                              # seal
                tris += cyl(list(h), [('C', i, u) for u in range(3)])  # tube to C_i
        tris += [tuple(Pj)]                              # filling E_j
        # sanity: coordinates of hole match ((t,0)+eta_u, 1)
        for t in range(d + 1):
            h = (s[t][0], s[t][1], s[t + 1][0])
            for u in range(3):
                assert pos[h[u]] == (Fr(t) + eta[u][0], eta[u][1], Fr(1))
        cols[j] = (tris, pos, rows)
    return cols, rowpos

def check_geometry(rng):
    tot = ok = 0
    cases = [(3, 3, {(i, j) for i in range(1, 4) for j in range(1, 4)})]
    for trial in range(6):
        r, k = rng.randint(1, 5), rng.randint(1, 3)
        P = {(i, j) for i in range(1, r + 1) for j in range(1, k + 1) if rng.random() < 0.55}
        cases.append((r, k, P))
    for (r, k, P) in cases:
        cols, rowpos = build_universe(r, k, P)
        allpos4 = {}
        for j, (tris, pos, rows) in cols.items():
            # distinct positions within the column
            verts = sorted({v for t in tris for v in t}, key=str)
            pts = [pos[v] for v in verts]
            assert len(set(pts)) == len(pts)
            # nondegenerate triangles
            for t in tris:
                assert cross(sub(pos[t[1]], pos[t[0]]), sub(pos[t[2]], pos[t[0]])) != (0, 0, 0)
            # pairwise proper intersection (all triangles, incl. seals, tubes, E_j)
            for T1, T2 in itertools.combinations(tris, 2):
                tot += 1
                ok += tri_pair_ok(T1, T2, pos)
            # z >= 0 and z = 0 only at row vertices of rows in P_{*j}; tube triangles at z=0 are edges/vertices of C_i
            for v in verts:
                assert pos[v][2] >= 0
                if pos[v][2] == 0:
                    assert v[0] == 'C' and v[1] in rows
            for v in verts:
                x, y, z = pos[v]
                p4 = (x, y, z, j * z)
                if v in allpos4:
                    assert allpos4[v] == p4
                allpos4[v] = p4
        # injectivity in R^4 across columns (row vertices shared by name)
        assert len(set(allpos4.values())) == len(allpos4)
        # row triangles D_i pairwise disjoint in B
        for i1, i2 in itertools.combinations(range(1, r + 1), 2):
            xs1 = [rowpos[('C', i1, u)][0] for u in range(3)]; xs2 = [rowpos[('C', i2, u)][0] for u in range(3)]
            assert max(xs1) < min(xs2)
    return ok, tot

if __name__ == "__main__":
    rng = random.Random(2026)
    a = check_s3(rng); print("lem:dual / thm:s3 formulas (F2,F3,F5):", a)
    b = check_banded(rng); print("thm:banded segment tree vs direct rank:", b)
    c = check_bandwidth(rng); print("cor:bandwidth width <= binom(b+1,q):", c)
    d = check_geometry(rng); print("lem:column pairwise proper triangle intersections:", d)
    print("ALL VALIDATED:", all(x[0] == x[1] and x[1] > 0 for x in (a, b, c, d)))
