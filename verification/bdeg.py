#!/usr/bin/env python3
"""bdeg.py -- brute-force verification of the BOUNDED-DEGREE gadget (lem:bdeg-crux, thm:bdeg = thm:bounded-degree).

Construction U^b(l1, l2) for the dense admissible set P = [l1] x [l2], built from the verified 7-toggle hole socket of
hole_gadget.py (switched version, with tethers).  A "triangle cycle" is three vertices and their three edges.
  * Row i has l2 copies C_i^1..C_i^{l2} (triangle cycles on fresh vertices); the copies C_i^j and C_i^{j+1} are joined
    by the 6-triangle annulus Q_i^j = Cyl(C_i^j, C_i^{j+1}) (dynrank.cylinder), which is ALWAYS present.
  * Column j: running triangle cycles s_0, s_1, ..., s_{l1+1} on fresh vertices; a cone on s_0; the tether socket
    s_0 -> s_1 whose hole is tubed to the private tether cycle P_j (always present); for each row i the socket
    s_i -> s_{i+1} (punctured cylinder Cyl(s_i, s_{i+1}) minus the hole h = (a0, a1, b0)) whose hole is SEALED by h
    (1 triangle) if M_ij = 0 and TUBED by Cyl(h, C_i^j) to the j-th copy of row i (6 triangles) if M_ij = 1;
    a cone on s_{l1+1}.
  * Kill switch of row i: a filling D_i of the FIRST copy C_i^1, either the single triangle C_i^1 ('fill') or a
    3-triangle cone whose apex and spoke edges are permanent ('cone').  Row i is active iff D_i is absent.
  * Activation switch of column j: a filling E_j of P_j ('fill' or 'cone').  Column j is active iff E_j is present.
  K(M;R,J) = all vertices and edges of the universe (fixed 1-skeleton) + the permanent triangles + for every (i,j)
  the seal (M_ij = 0) or the tube (M_ij = 1) + D_i for i not in R + E_j for j in J.  The universe U^b contains all
  seals, all tubes and all fillings.

Checks (every homology number by brute-force linear algebra; one output line per check):
  (1) F2: dim Z_2 = beta_2 = |J| - rank_F2 M[R,J]  (exhaustive for l1,l2 <= 2, plus random cases with l1,l2 in 1..4);
  (2) F3 (and F5) with ORIENTED boundary matrices: dim ker d_2 = |J| - rank_Fp M[R,J], incl. matrices whose F2 and F3
      ranks differ and all-ones matrices (which would expose inconsistent orientations);
  (3) Boolean OuMv identity [beta_2 < |J|] == [M[R,J] != 0] on every case of (1) and (2);
  (4) degrees in the universe for l1, l2 = 1..6 (and 8, 12, 16): max #triangles per edge, max #simplices per vertex;
  (5) a single entry flip changes exactly 7 triangles (all in socket (i,j)), never a vertex or an edge; a switch
      changes 1 ('fill') or 3 ('cone') triangles;
  (6) beta_1(K) = c_U + beta_2(K) - n_2(K), c_U = beta_0(U^(1)) - n_0(U) + n_1(U)  (eq. b1-from-b2), F2;
  (7) [extra: bounded degree for p >= 3] the suspension apex lies in |U|+1 simplices (unbounded), whereas the ordered
      product K x S^1 (S^1 = a triangle cycle) keeps bounded degree, satisfies beta_3(K x S^1) = beta_2(K), and turns
      one triangle update of K into a constant number of simplex updates.
  (8) [extra: sparse admissible sets] copies only at admissible positions: crux over F2/F3, same degree bounds,
      size O(l1 + l2 + |P|);
"""
import ast
import random
import sys
from collections import Counter
from itertools import combinations, product

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


def _socket_from_hole_gadget(s_prev, s_next, C, bit):
    """socket() of hole_gadget.py (verbatim copy): the punctured cylinder plus seal (bit 0) or tube (bit 1)."""
    cyl = cylinder(s_prev, s_next)
    h = (s_prev[0], s_prev[1], s_next[0])
    assert any(set(t) == set(h) for t in cyl)
    base = [t for t in cyl if set(t) != set(h)]
    return base + ([h] if bit == 0 else cylinder(list(h), C))

VARIANTS = [('fill', 'fill'), ('cone', 'cone'), ('fill', 'cone'), ('cone', 'fill')]   # (row kill cap, tether cap)


HG_SOCKET = _socket_from_hole_gadget


def fz(ts):
    return [frozenset(t) for t in ts]


def socket_parts(a, b, c):
    """(punctured cylinder, seal, tube) of the socket between a and b whose hole may be tubed to c."""
    h = (a[0], a[1], b[0])
    punct = [t for t in fz(cylinder(a, b)) if t != frozenset(h)]
    seal, tube = [frozenset(h)], fz(cylinder(list(h), c))
    assert len(punct) == 5 and len(tube) == 6
    assert set(punct + seal) == set(fz(HG_SOCKET(a, b, c, 0)))      # identical to the verified gadget
    assert set(punct + tube) == set(fz(HG_SOCKET(a, b, c, 1)))
    return punct, seal, tube


class Universe:
    """Universe U^b(P); P = admissible positions (default: all of [l1] x [l2]).  Row i gets one copy C_i^j for every
       admissible (i,j) (one dummy copy if row i has none), chained by annuli in increasing order of j."""
    def __init__(self, l1, l2, row_cap='fill', col_cap='fill', P=None):
        self.l1, self.l2, self.row_cap, self.col_cap = l1, l2, row_cap, col_cap
        P = set(product(range(l1), range(l2))) if P is None else set(P)
        self.nv, self.role = 0, {}
        self.perm, self.seal, self.tube, self.D, self.E = [], {}, {}, {}, {}
        C = {}
        for i in range(l1):
            cols = sorted(j for j in range(l2) if (i, j) in P) or [None]
            for q, j in enumerate(cols):
                C[(i, j)] = self.fresh(3, 'row copy C_i^j, %s copy of its row' % (
                    'only' if len(cols) == 1 else ('first' if q == 0 else ('last' if q == len(cols) - 1 else 'middle'))),
                    positional=True)
            for q in range(len(cols) - 1):
                self.perm += fz(cylinder(C[(i, cols[q])], C[(i, cols[q + 1])]))  # Q_i^j, always present
            self.D[i] = self.cap(C[(i, cols[0])], row_cap, 'kill-cap apex')      # kill switch on the FIRST copy
        for j in range(l2):
            rows = [i for i in range(l1) if (i, j) in P]
            P_j = self.fresh(3, 'tether P_j')
            s = self.fresh(3, 'running cycle s^j_0 (coned)', positional=True)
            self.perm += fz(disk(s, self.fresh(1, 'column cone apex')[0]))
            s_next = self.fresh(3, 'running cycle s^j_1 (after the tether socket)', positional=True)
            punct, _, tube = socket_parts(s, s_next, P_j)
            self.perm += punct + tube                                            # tether socket, always tubed
            s = s_next
            for q, i in enumerate(rows):
                s_next = self.fresh(3, 'running cycle s^j_{d_j+1} (coned)' if q == len(rows) - 1 else
                                    'running cycle s^j_t, 2<=t<=d_j (between two row sockets)', positional=True)
                punct, self.seal[(i, j)], self.tube[(i, j)] = socket_parts(s, s_next, C[(i, j)])
                self.perm += punct
                s = s_next
            self.perm += fz(disk(s, self.fresh(1, 'column cone apex')[0]))
            self.E[j] = self.cap(P_j, col_cap, 'tether-cap apex')
        self.all_tris = (self.perm + [t for x in self.seal.values() for t in x] + [t for x in self.tube.values() for t in x]
                         + [t for x in self.D.values() for t in x] + [t for x in self.E.values() for t in x])
        assert len(set(self.all_tris)) == len(self.all_tris)                    # pieces are triangle-disjoint
        self.skel = set()
        for t in self.all_tris:
            for v in t:
                self.skel.add(frozenset([v]))
            for e in combinations(t, 2):
                self.skel.add(frozenset(e))
        self.U = self.skel | set(self.all_tris)

    def fresh(self, n, role, positional=False):
        xs = list(range(self.nv, self.nv + n))
        self.nv += n
        for p, x in enumerate(xs):
            self.role[x] = role + ('[%d]' % p if positional else '')
        return xs

    def cap(self, c, mode, apex_role):
        return fz([tuple(c)]) if mode == 'fill' else fz(disk(c, self.fresh(1, apex_role)[0]))

    def tris(self, M, R, J):
        ts = list(self.perm)
        for (i, j) in self.seal:
            ts += self.tube[(i, j)] if M[i][j] else self.seal[(i, j)]
        for i in range(self.l1):
            if i not in R:
                ts += self.D[i]
        for j in J:
            ts += self.E[j]
        return ts

    def complex(self, M, R, J):
        return self.skel | set(self.tris(M, R, J))


_UCACHE = {}


def universe(l1, l2, variant):
    key = (l1, l2, variant)
    if key not in _UCACHE:
        _UCACHE[key] = Universe(l1, l2, *variant)
    return _UCACHE[key]


def sub(M, R, J):
    return [[M[i][j] for j in sorted(J)] for i in sorted(R)]


def rank_f2(A):
    return matrix_rank(A) if A and A[0] else 0


def rank_fp(A, p):
    return fp_rank([{c: 1 for c, x in enumerate(row) if x} for row in A], p) if A and A[0] else 0


def n_simp(K, d):
    return sum(1 for c in K if len(c) == d + 1)


# ------------------------------------------------------------------------------------------------------------------
fails = []
oumv_ok = oumv_tot = 0


def note(tag, ok, detail):
    if not ok and len(fails) < 25:
        fails.append('%s: %s' % (tag, detail))


# (1) + (3) + (6) over F2 ------------------------------------------------------------------------------------------
c1_ok = c1_tot = c6_ok = 0
cases1 = []
for variant in VARIANTS:                                                      # exhaustive, l1, l2 <= 2
    for l1, l2 in product([1, 2], repeat=2):
        for bits in product([0, 1], repeat=l1 * l2):
            M = [list(bits[i * l2:(i + 1) * l2]) for i in range(l1)]
            for rb in product([0, 1], repeat=l1):
                for jb in product([0, 1], repeat=l2):
                    cases1.append((variant, l1, l2, M, {i for i in range(l1) if rb[i]}, {j for j in range(l2) if jb[j]}))
n_exh = len(cases1)
rng = random.Random(20261102)
for t in range(160):                                                          # random, l1, l2 in 1..4
    l1, l2 = rng.randint(1, 4), rng.randint(1, 4)
    dens = rng.choice([0.3, 0.5, 0.8])
    M = [[int(rng.random() < dens) for _ in range(l2)] for _ in range(l1)]
    cases1.append((VARIANTS[t % 4], l1, l2, M, {i for i in range(l1) if rng.random() < .65},
                   {j for j in range(l2) if rng.random() < .65}))
for variant in VARIANTS:                                                      # adversarial
    cases1.append((variant, 4, 4, [[1] * 4 for _ in range(4)], set(range(4)), set(range(4))))
    cases1.append((variant, 3, 3, [[1, 1, 0], [0, 1, 1], [1, 0, 1]], set(range(3)), set(range(3))))
    cases1.append((variant, 4, 4, [[0] * 4 for _ in range(4)], set(range(4)), set(range(4))))

for (variant, l1, l2, M, R, J) in cases1:
    u = universe(l1, l2, variant)
    K = u.complex(M, R, J)
    T = n_simp(K, 2)
    z2 = T - boundary_rank(K, 2)
    b0, b1, b2, b3 = betti(K)
    want = len(J) - rank_f2(sub(M, R, J))
    ok = (z2 == b2 == want) and b3 == 0
    c1_tot += 1
    c1_ok += ok
    note('(1)', ok, 'variant=%s M=%s R=%s J=%s dimZ2=%d beta2=%d want=%d' % (variant, M, R, J, z2, b2, want))
    nonzero = any(M[i][j] for i in R for j in J)
    oumv_tot += 1
    oumv_ok += (int(b2 < len(J)) == int(nonzero))
    note('(3)/F2', int(b2 < len(J)) == int(nonzero), 'variant=%s M=%s R=%s J=%s' % (variant, M, R, J))
    nU0, nU1 = n_simp(u.skel, 0), n_simp(u.skel, 1)
    if not hasattr(u, 'cU'):
        u.cU = (nU0 - boundary_rank(u.skel, 1)) - nU0 + nU1
    ok6 = (b1 == u.cU + b2 - T) and n_simp(K, 0) == nU0 and n_simp(K, 1) == nU1
    c6_ok += ok6
    note('(6)', ok6, 'variant=%s M=%s R=%s J=%s b1=%d cU=%d b2=%d T=%d' % (variant, M, R, J, b1, u.cU, b2, T))
print('(1) F2 crux, bounded-degree gadget: dim Z_2 = beta_2 = |J| - rank_F2 M[R,J] on %d/%d cases '
      '(%d exhaustive l1,l2<=2 over 4 cap variants + %d random l1,l2 in 1..4 + 12 adversarial)'
      % (c1_ok, c1_tot, n_exh, 160))

# (2) + (3) over F3 / F5 with oriented boundary matrices ------------------------------------------------------------
c2 = {3: [0, 0], 5: [0, 0]}
f2_vs_f3_differ = 0
cases2 = []
rng = random.Random(7)
for t in range(48):
    l1, l2 = rng.randint(1, 4), rng.randint(1, 4)
    M = [[rng.randint(0, 1) for _ in range(l2)] for _ in range(l1)]
    cases2.append((VARIANTS[t % 4], l1, l2, M, {i for i in range(l1) if rng.random() < .65},
                   {j for j in range(l2) if rng.random() < .65}))
for variant in VARIANTS:
    cases2.append((variant, 3, 3, [[1, 1, 0], [0, 1, 1], [1, 0, 1]], set(range(3)), set(range(3))))   # rk2=2, rk3=3
    cases2.append((variant, 3, 4, [[1, 1, 0, 1], [0, 1, 1, 1], [1, 0, 1, 0]], set(range(3)), set(range(4))))
    cases2.append((variant, 4, 4, [[1] * 4 for _ in range(4)], set(range(4)), set(range(4))))         # all ones
    cases2.append((variant, 2, 3, [[1, 1, 1], [1, 1, 1]], {0, 1}, {0, 2}))
for (variant, l1, l2, M, R, J) in cases2:
    u = universe(l1, l2, variant)
    K = u.complex(M, R, J)
    T = n_simp(K, 2)
    S = sub(M, R, J)
    f2_vs_f3_differ += (rank_f2(S) != rank_fp(S, 3))
    for p in (3, 5):
        z2 = T - oriented_d2_rank(K, p)
        want = len(J) - rank_fp(S, p)
        c2[p][1] += 1
        c2[p][0] += (z2 == want)
        note('(2)/F%d' % p, z2 == want, 'variant=%s M=%s R=%s J=%s dimZ2=%d want=%d' % (variant, M, R, J, z2, want))
        nonzero = any(M[i][j] for i in R for j in J)
        oumv_tot += 1
        oumv_ok += (int(z2 < len(J)) == int(nonzero))
        note('(3)/F%d' % p, int(z2 < len(J)) == int(nonzero), 'variant=%s M=%s R=%s J=%s' % (variant, M, R, J))
print('(2) F3 oriented crux: dim ker d_2 = |J| - rank_F3 M[R,J] on %d/%d cases (F5: %d/%d); '
      '%d cases have rank_F2 != rank_F3, so F2 and F3 answers genuinely differ there'
      % (c2[3][0], c2[3][1], c2[5][0], c2[5][1], f2_vs_f3_differ))
print('(3) Boolean OuMv identity [beta_2 < |J|] == [M[R,J] != 0]: %d/%d (all cases of (1) over F2, of (2) over F3 and F5)'
      % (oumv_ok, oumv_tot))


# (4) degrees in the universe ----------------------------------------------------------------------------------------
def degree_stats(Ucells, role=None):
    tpe, star, edeg, tdeg = Counter(), Counter(), Counter(), Counter()
    for c in Ucells:
        for v in c:
            star[v] += 1
        if len(c) == 2:
            for v in c:
                edeg[v] += 1
        elif len(c) == 3:
            for v in c:
                tdeg[v] += 1
            for e in combinations(c, 2):
                tpe[frozenset(e)] += 1
    ms = max(star.values())
    arg = sorted({role[v] for v in star if star[v] == ms}) if role else None
    return max(tpe.values()), ms, max(edeg.values()), max(tdeg.values()), arg


def poly_str(a, b, c, d):
    out = '%d*l1*l2' % a
    for coef, name in ((b, 'l1'), (c, 'l2'), (d, '')):
        if coef:
            out += (' + ' if coef > 0 else ' - ') + ('%d*%s' % (abs(coef), name) if name else '%d' % abs(coef))
    return out


c4_ok = True
deg_table = {}
size_table = {}
for variant in VARIANTS:
    for l1, l2 in list(product(range(1, 7), repeat=2)) + [(8, 8), (12, 12), (16, 16), (16, 1), (1, 16)]:
        u = Universe(l1, l2, *variant)
        deg_table[(variant, l1, l2)] = degree_stats(u.U, u.role)
        size_table[(variant, l1, l2)] = (len(u.U), n_simp(u.U, 0), n_simp(u.U, 1), n_simp(u.U, 2))
summary4 = []
for variant in VARIANTS:
    rows = {k[1:]: v for k, v in deg_table.items() if k[0] == variant}
    gmax = tuple(max(v[q] for v in rows.values()) for q in range(4))
    stable = all(rows[(a, b)][:4] == rows[(3, 3)][:4] for (a, b) in rows if a >= 3 and b >= 3)
    attained_small = rows[(3, 3)][:4] == gmax
    c4_ok &= stable and attained_small and gmax[0] == 3
    # exact size formula n(U) = x*l1*l2 + y*l1 + z*l2 + w, fitted on 4 points and checked on all
    pts = {k[1:]: v[0] for k, v in size_table.items() if k[0] == variant}
    # n(l1, l2) is bilinear: recover the coefficients by finite differences, then check on every size
    xy = pts[(2, 2)] - pts[(1, 2)] - pts[(2, 1)] + pts[(1, 1)]
    y_ = pts[(2, 1)] - pts[(1, 1)] - xy
    z_ = pts[(1, 2)] - pts[(1, 1)] - xy
    w_ = pts[(1, 1)] - xy - y_ - z_
    formula_ok = all(pts[(a, b)] == xy * a * b + y_ * a + z_ * b + w_ for (a, b) in pts)
    c4_ok &= formula_ok
    summary4.append('%s/%s caps: max tri/edge=%d, max simplices/vertex=%d (max edges/vertex=%d, max tri/vertex=%d; '
                    'attained only by: %s), identical for all l1,l2>=3 up to 16: %s; |U| = %s (exact on all sizes: %s)'
                    % (variant[0], variant[1], gmax[0], gmax[1], gmax[2], gmax[3], '; '.join(rows[(3, 3)][4]),
                       stable, poly_str(xy, y_, z_, w_), formula_ok))
    if variant in (('fill', 'fill'), ('cone', 'cone')):
        summary4.append('%s/%s max simplices/vertex for l1=1..6 (rows) x l2=1..6 (cols): %s'
                        % (variant[0], variant[1], [[rows[(a, b)][1] for b in range(1, 7)] for a in range(1, 7)]))
print('(4) universe degrees for l1,l2 in 1..6 (+8,12,16): ' + ' | '.join(summary4))

# (5) locality ------------------------------------------------------------------------------------------------------
rng = random.Random(55)
flip_counts, sw_counts, c5_ok, c5_tot = Counter(), Counter(), 0, 0
for t in range(200):
    variant = VARIANTS[t % 4]
    l1, l2 = rng.randint(1, 6), rng.randint(1, 6)
    u = universe(l1, l2, variant)
    M = [[rng.randint(0, 1) for _ in range(l2)] for _ in range(l1)]
    R = {i for i in range(l1) if rng.random() < .5}
    J = {j for j in range(l2) if rng.random() < .5}
    i, j = rng.randrange(l1), rng.randrange(l2)
    M2 = [row[:] for row in M]
    M2[i][j] ^= 1
    K1, K2 = u.complex(M, R, J), u.complex(M2, R, J)
    d = K1 ^ K2
    local = set(u.seal[(i, j)]) | set(u.tube[(i, j)])
    ok = len(d) == 7 and all(len(c) == 3 for c in d) and d <= local
    flip_counts[len(d)] += 1
    i2, j2 = rng.randrange(l1), rng.randrange(l2)
    dr = u.complex(M, R ^ {i2}, J) ^ K1
    dc = u.complex(M, R, J ^ {j2}) ^ K1
    want_r = 1 if variant[0] == 'fill' else 3
    want_c = 1 if variant[1] == 'fill' else 3
    ok = ok and len(dr) == want_r and len(dc) == want_c and all(len(c) == 3 for c in dr | dc)
    sw_counts[('row', variant[0], len(dr))] += 1
    sw_counts[('col', variant[1], len(dc))] += 1
    c5_tot += 1
    c5_ok += ok
    note('(5)', ok, 'variant=%s flip diff=%d row-switch diff=%d col-switch diff=%d' % (variant, len(d), len(dr), len(dc)))
print('(5) locality: entry flip changes exactly 7 triangles (seal <-> tube of socket (i,j)), 0 vertices/edges, on %d/%d '
      'random flips (diff-size histogram %s); switch = 1 triangle (fill) / 3 triangles (cone): %s'
      % (c5_ok, c5_tot, dict(flip_counts), dict(sorted(sw_counts.items()))))
print('(6) beta_1 = c_U + beta_2 - n_2 with fixed 1-skeleton (eq. b1-from-b2), F2: %d/%d' % (c6_ok, c1_tot))


# (7) extra: bounded degree for every p >= 3 (product with a circle instead of suspension) -------------------------------
def product_with_circle(K):
    """Ordered simplicial product K x S^1, S^1 = triangle cycle on {0,1,2}: simplices = chains
       (v_0,w_0) < ... < (v_m,w_m) with v_0 <= ... <= v_m spanning a simplex of K, w_0 <= ... <= w_m spanning one of S^1."""
    Lsimp = [(0,), (1,), (2,), (0, 1), (1, 2), (0, 2)]
    out = set()
    for s in K:
        sv = sorted(s)
        for tv in Lsimp:
            a, b = len(sv) - 1, len(tv) - 1
            for ups in combinations(range(a + b), b):                     # lattice paths (0,0) -> (a,b)
                x = y = 0
                chain = [(sv[0], tv[0])]
                for step in range(a + b):
                    if step in ups:
                        y += 1
                    else:
                        x += 1
                    chain.append((sv[x], tv[y]))
                for r in range(1, len(chain) + 1):
                    for c in combinations(chain, r):
                        out.add(frozenset(c))
    return out


c7_ok, c7_tot, toggles7 = 0, 0, Counter()
rng = random.Random(77)
for t in range(8):
    variant = VARIANTS[t % 4]
    l1, l2 = rng.randint(1, 2), rng.randint(1, 3)
    u = universe(l1, l2, variant)
    M = [[rng.randint(0, 1) for _ in range(l2)] for _ in range(l1)]
    R = {i for i in range(l1) if rng.random() < .6}
    J = {j for j in range(l2) if rng.random() < .7}
    K = u.complex(M, R, J)
    KS = product_with_circle(K)
    b = betti(KS)
    want = len(J) - rank_f2(sub(M, R, J))
    sigma = rng.choice(sorted((c for c in K if len(c) == 3), key=sorted))
    tog = len(KS ^ product_with_circle(K - {sigma}))
    toggles7[tog] += 1
    c7_tot += 1
    c7_ok += (b[3] == want) and tog == 18
    note('(7)', (b[3] == want) and tog == 18, 'beta(KxS1)=%s want beta3=%d toggles=%d' % (b, want, tog))
ps_deg = {}
for l1, l2 in product(range(1, 5), repeat=2):
    u = universe(l1, l2, ('cone', 'cone'))
    ps_deg[(l1, l2)] = degree_stats(product_with_circle(u.U))[1]
ps_stable = all(ps_deg[k] == ps_deg[(3, 3)] for k in ps_deg if min(k) >= 3) and max(ps_deg.values()) == ps_deg[(3, 3)]
susp_apex = {k: len(universe(k[0], k[1], ('cone', 'cone')).U) + 1 for k in [(1, 1), (2, 2), (4, 4)]}
c7_all = c7_ok == c7_tot and ps_stable
print('(7) [extra] suspension apex lies in |U|+1 simplices (%s: unbounded), but U x S^1 has max %d simplices/vertex '
      '(cone/cone caps, l1,l2<=4, stable: %s), beta_3(K x S^1) = beta_2(K) = |J| - rank M[R,J] and one triangle update '
      'of K = %s simplex updates of K x S^1: %d/%d'
      % (', '.join('l=%s: %d' % (k, v) for k, v in susp_apex.items()), ps_deg[(3, 3)], ps_stable, dict(toggles7),
         c7_ok, c7_tot))

# (8) extra: sparse admissible sets P (copies only at admissible positions): crux + size O(l1 + l2 + |P|) --------------
rng = random.Random(88)
c8_ok = c8_tot = 0
ratio = 0.0
for t in range(60):
    variant = VARIANTS[t % 4]
    l1, l2 = rng.randint(1, 5), rng.randint(1, 5)
    P = {(i, j) for i in range(l1) for j in range(l2) if rng.random() < 0.45}
    u = Universe(l1, l2, *variant, P=P)
    M = [[int((i, j) in P and rng.random() < 0.6) for j in range(l2)] for i in range(l1)]
    R = {i for i in range(l1) if rng.random() < .65}
    J = {j for j in range(l2) if rng.random() < .65}
    K = u.complex(M, R, J)
    T = n_simp(K, 2)
    S = sub(M, R, J)
    ok = (T - boundary_rank(K, 2) == len(J) - rank_f2(S)) and (T - oriented_d2_rank(K, 3) == len(J) - rank_fp(S, 3))
    ok = ok and degree_stats(u.U)[0] <= 3 and degree_stats(u.U)[1] <= 23
    ratio = max(ratio, len(u.U) / (l1 + l2 + len(P)))
    c8_tot += 1
    c8_ok += ok
    note('(8)', ok, 'variant=%s P=%s M=%s R=%s J=%s' % (variant, sorted(P), M, R, J))
print('(8) [extra] sparse admissible sets P (row i has copies only at its admissible positions): F2 and F3 crux, '
      '<=3 triangles/edge, <=23 simplices/vertex on %d/%d random (P, M, R, J); max |U|/(l1+l2+|P|) = %.1f'
      % (c8_ok, c8_tot, ratio))

allv = (c1_ok == c1_tot and c2[3][0] == c2[3][1] and c2[5][0] == c2[5][1] and oumv_ok == oumv_tot and c4_ok
        and c5_ok == c5_tot and c6_ok == c1_tot and c7_all and c8_ok == c8_tot)
for f in fails:
    print('FAIL', f)
print('ALL VALIDATED:', allv)
