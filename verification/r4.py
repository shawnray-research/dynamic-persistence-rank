#!/usr/bin/env python3
"""r4.py -- exact verification of an explicit LINEAR embedding of the dense 'hole gadget' universe
(r x k matrix) in R^4: a 3D page model in the half-space H = {z >= 0}, one page per column, glued
along the binding plane z = 0 where the row triangles C_i (and their fillings D_i) live.

Standard library only; all arithmetic exact (fractions.Fraction).  Run:  python3 -I r4.py

Method.  For simplices S, T (affinely independent vertex sets) with common vertex set K, the hulls
meet properly, i.e. conv(S) & conv(T) == conv(K), iff the exact LP
      max  sum_{v in S\\K} lam_v
      s.t. sum_S lam_v p_v = sum_T mu_w p_w,  sum lam = sum mu = 1,  lam, mu >= 0
is infeasible with K empty, or has optimum 0 (uniqueness of barycentric coordinates).  This covers
coplanar / collinear / touching configurations uniformly.  The LP is solved by an exact two-phase
simplex method with Bland's rule.  An exact bounding-box test is used only as a shortcut for pairs
with no common vertex (disjoint boxes => disjoint hulls).  A self-test first confirms that the
checker flags known improper configurations (coplanar overlaps, crossings, vertex-in-face, ...).

Second part ("paper scheme", paper_main): the coordinates exactly as stated in paper/easy.tex
(paragraph "One column." / Lemma lem:column, "The open book" / Theorem thm:r4(i)) for GENERAL admissible
sets P in [r]x[k]: s_{t,u}=(t,delta_u), (P_j)_(u)=(eta_u/2,1/2), (C_i)_(u)=((i,0)+eta_u/2,0), apexes
(-1,1/2,3/2), (d+2,1/2,3/2), tubes Cyl(h_t,C_{i_t}), pages phi_j(x,y,z)=(x,y,z,jz).  Checks: (1) every
possible page for r<=4 (all row sets S of [r]; W incl. the seal of h_0, plus all C_i and D_i): all simplex
pairs proper; (2) each page meets z=0 exactly in its row cycles; text claims (eq:section etc.); 24 random
P (r,k<=4) looked up page by page; (3) full R^4 assembly: direct exact check of all triangle pairs for 8
P with r,k<=3, plus the analytic argument (exact linear algebra for the pages + (1),(2)); (4) realized
triangle set == U(P) of Definition def:gadget (paper/equiv.tex), with counts.  Negative controls included.
"""
import itertools
import random
import sys
import time
from fractions import Fraction as Fr

HALF = Fr(1, 2)

# ----------------------------------------------------------------------------- construction parameters
ROW_SHRINK = Fr(1, 2)      # C_i = hole h_i shrunk about its centroid by this factor ...
ROW_Z = Fr(0)              # ... and moved to the binding plane z = 0
TETHER_SHRINK = Fr(1, 2)   # P_j = hole h_0 shrunk about its centroid by this factor ...
TETHER_Z = Fr(1, 2)        # ... at height z = 1/2
CIRCLE = [(Fr(3, 5), Fr(4, 5)), (Fr(0), Fr(1)), (Fr(-3, 5), Fr(4, 5)),
          (Fr(5, 13), Fr(12, 13)), (Fr(-5, 13), Fr(12, 13))]
CASES = [(1, 1), (2, 2), (3, 3), (3, 1), (1, 3)]
DIRECT_R4_MAX = 3          # direct R^4 LP check on all triangle pairs when r, k <= this
if '--spec-min' in sys.argv:  # (the spec only requires r, k <= 2; default runs it for every case, ~10 s)
    DIRECT_R4_MAX = 2


# ----------------------------------------------------------------------------- exact LP (simplex, Bland)
def _pivot(T, basis, r, e):
    pr = T[r]
    pv = pr[e]
    if pv != 1:
        pr = [x / pv for x in pr]
        T[r] = pr
    for i, Ti in enumerate(T):
        if i != r:
            f = Ti[e]
            if f:
                T[i] = [a - f * b for a, b in zip(Ti, pr)]
    basis[r] = e


def _simplex(T, basis, cost, nallowed):
    """Primal simplex, Bland's rule, maximize cost.x; only columns < nallowed may enter.
    Returns True (optimal) or False (unbounded)."""
    m = len(T)
    while True:
        bset = set(basis)
        enter = -1
        for j in range(nallowed):
            if j in bset:
                continue
            rc = cost[j]
            for i in range(m):
                cb = cost[basis[i]]
                if cb:
                    rc -= cb * T[i][j]
            if rc > 0:
                enter = j
                break
        if enter < 0:
            return True
        bi, br = -1, None
        for i in range(m):
            a = T[i][enter]
            if a > 0:
                q = T[i][-1] / a
                if bi < 0 or q < br or (q == br and basis[i] < basis[bi]):
                    bi, br = i, q
        if bi < 0:
            return False
        _pivot(T, basis, bi, enter)


def lp_max(A, b, c):
    """Exact LP: maximize c.x s.t. A x = b, x >= 0.  None if infeasible, else the optimum (Fraction)."""
    m, n = len(A), len(c)
    T = []
    for i in range(m):
        row = [Fr(x) for x in A[i]] + [Fr(0)] * m + [Fr(b[i])]
        if row[-1] < 0:
            row = [-x for x in row]
        row[n + i] = Fr(1)
        T.append(row)
    basis = [n + i for i in range(m)]
    cost1 = [Fr(0)] * n + [Fr(-1)] * m
    if not _simplex(T, basis, cost1, n + m):
        raise RuntimeError('phase 1 unbounded (impossible)')
    if sum(cost1[basis[i]] * T[i][-1] for i in range(m)) < 0:
        return None
    i = 0
    while i < len(T):                      # drive zero-level artificials out, drop redundant rows
        if basis[i] >= n:
            for j in range(n):
                if T[i][j] != 0:
                    _pivot(T, basis, i, j)
                    break
            else:
                del T[i]
                del basis[i]
                continue
        i += 1
    cost2 = [Fr(x) for x in c] + [Fr(0)] * m
    if not _simplex(T, basis, cost2, n):
        raise RuntimeError('LP unbounded (impossible: feasible set is a polytope)')
    return sum(cost2[basis[i]] * T[i][-1] for i in range(len(T)))


# ----------------------------------------------------------------------------- geometric predicates
def improper(S, T, P):
    """True iff conv(S) & conv(T) != conv(S & T).  S, T: tuples of labels, each affinely independent."""
    K = set(S) & set(T)
    if len(K) == len(S) or len(K) == len(T):
        return False                       # one is a face of the other
    d = len(P[S[0]])
    A = [[P[v][q] for v in S] + [-P[w][q] for w in T] for q in range(d)]
    A.append([1] * len(S) + [0] * len(T))
    A.append([0] * len(S) + [1] * len(T))
    b = [0] * d + [1, 1]
    c = [0 if v in K else 1 for v in S] + [0] * len(T)
    val = lp_max(A, b, c)
    if val is None:
        if K:
            raise RuntimeError('LP infeasible although the simplices share a vertex')
        return False
    return val > 0


def rank_of(vecs):
    M = [list(v) for v in vecs]
    rank = 0
    ncol = len(M[0]) if M else 0
    for col in range(ncol):
        piv = next((i for i in range(rank, len(M)) if M[i][col] != 0), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        for i in range(len(M)):
            if i != rank and M[i][col] != 0:
                f = M[i][col] / M[rank][col]
                M[i] = [a - f * b2 for a, b2 in zip(M[i], M[rank])]
        rank += 1
    return rank


def aff_indep(S, P):
    p0 = P[S[0]]
    vecs = [tuple(a - b for a, b in zip(P[v], p0)) for v in S[1:]]
    return rank_of(vecs) == len(vecs) if vecs else True


def coplanar(pts):
    p0 = pts[0]
    return rank_of([tuple(a - b for a, b in zip(p, p0)) for p in pts[1:]]) <= 2


def bbox(S, P):
    d = len(P[S[0]])
    return (tuple(min(P[v][q] for v in S) for q in range(d)),
            tuple(max(P[v][q] for v in S) for q in range(d)))


def boxes_disjoint(b1, b2):
    return any(b1[1][q] < b2[0][q] or b2[1][q] < b1[0][q] for q in range(len(b1[0])))


def check_pairs(simps, P, pair_filter=None):
    """All unordered pairs of distinct simplices (optionally filtered); returns (#pairs, #LPs, bad list)."""
    boxes = {s: bbox(s, P) for s in simps}
    npairs = nlp = 0
    bad = []
    for S, T in itertools.combinations(simps, 2):
        if pair_filter is not None and not pair_filter(S, T):
            continue
        npairs += 1
        if not (set(S) & set(T)) and boxes_disjoint(boxes[S], boxes[T]):
            continue
        nlp += 1
        if improper(S, T, P):
            bad.append((S, T))
    return npairs, nlp, bad


def self_test():
    """The checker must accept proper and reject improper configurations (incl. coplanar ones)."""
    P = {}

    def pt(name, *xyz):
        P[name] = tuple(Fr(x) for x in xyz)
    pt('o', 0, 0, 0); pt('a', 1, 0, 0); pt('b', 0, 1, 0); pt('c', 1, 1, 0); pt('d', 0, -1, 0)
    pt('e', -1, 2, 0); pt('f', 0, 0, 1); pt('g', Fr(1, 3), Fr(1, 3), 0); pt('h', Fr(1, 2), Fr(1, 2), 0)
    pt('p', Fr(1, 4), Fr(1, 4), -1); pt('q', Fr(1, 4), Fr(1, 4), 1); pt('s', 3, 3, 0); pt('t', 2, 0, 0)
    pt('u', -1, -1, 0); pt('w', 5, 5, 5); pt('x', 0, 2, 0)
    cases = [  # (S, T, expected improper?)
        (('o', 'a', 'b'), ('o', 'a', 'c'), True),    # coplanar, share an edge, overlap
        (('o', 'a', 'b'), ('o', 'a', 'd'), False),   # coplanar, share an edge, opposite sides
        (('o', 'a', 'b'), ('o', 'c', 'e'), True),    # coplanar, share a vertex, overlap
        (('o', 'a', 'b'), ('o', 'a', 'f'), False),   # share an edge, different planes
        (('o', 'a', 'b'), ('p', 'q', 's'), True),    # piercing, no common vertex
        (('g',), ('o', 'a', 'b'), True),             # vertex inside a triangle
        (('h',), ('o', 'a', 'b'), True),             # vertex on an edge
        (('a', 'b'), ('o', 'c'), True),              # crossing edges
        (('o', 'a'), ('o', 't'), True),              # collinear overlapping edges sharing a vertex
        (('o', 'a'), ('o', 'u'), False),             # edges meeting only at o
        (('o', 'a', 'b'), ('o', 'u', 'd'), False),   # coplanar, touch only at o
        (('o', 'a', 'b'), ('w', 's', 'x'), False),   # far apart
        (('o', 'a', 'b'), ('h', 'c', 'w'), True),    # touch at a boundary point that is not a vertex
        (('a', 'b', 'f'), ('o', 'c', 'w'), True),    # the segment o-c pierces triangle abf
    ]
    ok = all(improper(S, T, P) == exp for S, T, exp in cases)
    P4 = {k: v + (Fr(0),) for k, v in P.items()}     # same cases lifted into R^4
    ok = ok and all(improper(S, T, P4) == exp for S, T, exp in cases)
    return ok, len(cases)


# ----------------------------------------------------------------------------- combinatorial complex
def cyl(a, b):
    out = []
    for t in range(3):
        out.append((a[t], a[(t + 1) % 3], b[t]))
        out.append((a[(t + 1) % 3], b[t], b[(t + 1) % 3]))
    return out


def column_triangles(j, r):
    """Tagged triangles of column j (dense universe: every socket t >= 1 has BOTH seal and tube)."""
    s = [[('s', j, m, u) for u in range(3)] for m in range(r + 2)]
    A0, A1 = ('A', j, 0), ('A', j, 1)
    Pj = [('P', j, u) for u in range(3)]
    tris = []
    for u in range(3):
        tris.append(('cone', (A0, s[0][u], s[0][(u + 1) % 3])))
        tris.append(('cone', (A1, s[r + 1][u], s[r + 1][(u + 1) % 3])))
    for t in range(r + 1):
        h = (s[t][0], s[t][1], s[t + 1][0])
        cy = cyl(s[t], s[t + 1])
        assert cy[0] == h
        rest = [x for x in cy if set(x) != set(h)]
        assert len(rest) == 5
        tris += [('socket', x) for x in rest]
        if t == 0:
            tris += [('tube', x) for x in cyl(h, Pj)]          # tether tube
        else:
            tris.append(('seal', h))
            tris += [('tube', x) for x in cyl(h, [('C', t, u) for u in range(3)])]
    tris.append(('E', tuple(Pj)))
    return tris


def row_triangles(r):
    return [('D', tuple(('C', i, u) for u in range(3))) for i in range(1, r + 1)]


def cycle_edges(r, cols):
    cyc = []
    for i in range(1, r + 1):
        cyc.append([('C', i, u) for u in range(3)])
    for j in cols:
        cyc.append([('P', j, u) for u in range(3)])
        for m in range(r + 2):
            cyc.append([('s', j, m, u) for u in range(3)])
        for t in range(r + 1):
            cyc.append([('s', j, t, 0), ('s', j, t, 1), ('s', j, t + 1, 0)])
    E = set()
    for c in cyc:
        for u in range(3):
            E.add(tuple(sorted((c[u], c[(u + 1) % 3]))))
    return E


def closure(tris, extra_edges=()):
    T = {tuple(sorted(t)) for t in tris}
    E = set(extra_edges)
    for t in T:
        E.update(itertools.combinations(t, 2))
    V = {(v,) for e in E for v in e}
    return sorted(V), sorted(E), sorted(T)


# ----------------------------------------------------------------------------- coordinates
def hole_pts(t):
    return [(Fr(t), Fr(0), Fr(1)), (Fr(t), Fr(1), Fr(1)), (Fr(t + 1), Fr(0), Fr(1))]


def shrink(pts, f, z):
    cx = sum(p[0] for p in pts) / 3
    cy = sum(p[1] for p in pts) / 3
    return [(cx + f * (p[0] - cx), cy + f * (p[1] - cy), Fr(z)) for p in pts]


def model_coord(lab, r):
    """3D page-model coordinates (identical for every column)."""
    kind = lab[0]
    if kind == 's':
        m, u = lab[2], lab[3]
        return ((Fr(m), Fr(0), Fr(1)), (Fr(m), Fr(1), Fr(1)), (Fr(m), HALF, Fr(2)))[u]
    if kind == 'A':
        return (Fr(-1), HALF, Fr(3, 2)) if lab[2] == 0 else (Fr(r + 2), HALF, Fr(3, 2))
    if kind == 'P':
        return shrink(hole_pts(0), TETHER_SHRINK, TETHER_Z)[lab[2]]
    if kind == 'C':
        return shrink(hole_pts(lab[1]), ROW_SHRINK, ROW_Z)[lab[2]]
    raise ValueError(lab)


def phi(j, p):
    c, s = CIRCLE[j]
    return (p[0], p[1], p[2] * c, p[2] * s)


# ----------------------------------------------------------------------------- checks
def show(S, P):
    return '{' + ', '.join('%s@(%s)' % ('/'.join(map(str, v)), ','.join(map(str, P[v]))) for v in S) + '}'


def page_check(r):
    """Checks (1), (2) and the geometric-description part of (3) on the 3D model of one page."""
    ctris = column_triangles(0, r)
    rtris = row_triangles(r)
    tris = [t for _, t in ctris] + [t for _, t in rtris]
    cyc = cycle_edges(r, [0])
    V, E, T = closure(tris, cyc)
    _, E0, _ = closure(tris)
    P = {v[0]: model_coord(v[0], r) for v in V}
    res = {}
    # (1) geometric simplicial complex
    pts = [P[v[0]] for v in V]
    distinct = len(set(pts)) == len(pts)
    nondeg = all(aff_indep(t, P) for t in T) and all(aff_indep(e, P) for e in E)
    simps = V + E + T
    t0 = time.time()
    npairs, nlp, bad = check_pairs(simps, P)
    res['1'] = (distinct and nondeg and not bad,
                'V=%d E=%d T=%d; vertices distinct: %s; no degenerate edge/triangle: %s; '
                'all %d simplex pairs (incl. vertex/edge/triangle, coplanar) proper: %s '
                '[%d exact LPs, %.1fs]; cycle edges already edges of triangles: %s'
                % (len(V), len(E), len(T), distinct, nondeg, npairs, not bad, nlp, time.time() - t0,
                   cyc <= set(E0)),
                [(show(S, P), show(Tt, P)) for S, Tt in bad[:10]], len(bad))
    # (2) binding plane z = 0
    expected = set()
    for i in range(1, r + 1):
        C = tuple(sorted(('C', i, u) for u in range(3)))
        expected.add(C)
        expected.update(itertools.combinations(C, 2))
        expected.update((v,) for v in C)
    zpos = all(P[v[0]][2] >= 0 for v in V)
    Z0 = {s for s in simps if all(P[v][2] == 0 for v in s)}
    touch = [s for s in simps if any(P[v][2] == 0 for v in s)
             and tuple(v for v in s if P[v][2] == 0) not in expected]
    res['2'] = (zpos and Z0 == expected and not touch,
                'all vertices have z >= 0: %s; simplices inside z=0 = exactly {C_i vertices, C_i edges, D_i} '
                '(%d simplices): %s; every other simplex meets z=0 only in a C_i/D_i face: %s'
                % (zpos, len(Z0), Z0 == expected, not touch),
                [show(s, P) for s in touch[:10]])
    # (3, geometric part) coordinates match the description
    geo = []
    s = lambda m, u: ('s', 0, m, u)
    for t in range(r + 1):
        h = (s(t, 0), s(t, 1), s(t + 1, 0))
        geo.append([P[v] for v in h] == hole_pts(t))                       # hole/seal at z=1 as stated
        cy = cyl([s(t, u) for u in range(3)], [s(t + 1, u) for u in range(3)])
        for q in range(3):                                                   # lateral quads of the prism
            geo.append(coplanar([P[v] for v in set(cy[2 * q]) | set(cy[2 * q + 1])]))
        other = [('P', 0, u) for u in range(3)] if t == 0 else [('C', t, u) for u in range(3)]
        tb = cyl(h, other)
        for q in range(3):                                                   # frustum lateral faces planar
            geo.append(coplanar([P[v] for v in set(tb[2 * q]) | set(tb[2 * q + 1])]))
        geo.append(all(P[v][2] == (TETHER_Z if t == 0 else ROW_Z) for v in other))
    res['3geo'] = all(geo)
    return res


def counts_check(r, k):
    per = {}
    total = 0
    alltris = []
    for j in range(k):
        ct = column_triangles(j, r)
        cnt = {}
        for tag, t in ct:
            cnt[tag] = cnt.get(tag, 0) + 1
            alltris.append(t)
        per[j] = cnt
        total += len(ct)
    rt = row_triangles(r)
    alltris += [t for _, t in rt]
    total += len(rt)
    exp = {'cone': 6, 'socket': 5 * (r + 1), 'seal': r, 'tube': 6 * (r + 1), 'E': 1}
    ok = all(per[j] == exp for j in range(k)) and len(rt) == r
    nodup = len({frozenset(t) for t in alltris}) == len(alltris)
    exp_total = k * (12 * r + 18) + r
    V, E, T = closure(alltris, cycle_edges(r, range(k)))
    chi = len(V) - len(E) + len(T)
    ok = ok and nodup and total == exp_total and chi == 2 * k + r
    return ok, ('per column: cones %d, sockets %d, seals %d, tubes %d (incl. tether), E_j %d; D_i %d; '
                'total triangles %d (expected k(12r+18)+r = %d); no duplicate triangles: %s; '
                'full complex V=%d E=%d T=%d, chi=%d (expected 2k+r = %d)'
                % (per[0]['cone'], per[0]['socket'], per[0]['seal'], per[0]['tube'], per[0]['E'], len(rt),
                   total, exp_total, nodup, len(V), len(E), len(T), chi, 2 * k + r))


def r4_check(r, k, page_ok, direct):
    """(4) cross-page: analytic reduction always; direct exact LP on triangle pairs in R^4 if `direct`."""
    pts = CIRCLE[:k]
    circ = all(c * c + s * s == 1 and s >= 0 for c, s in pts) and len(set(pts)) == k
    # Lemma: phi_j(x,y,z) = phi_j'(x',y',z') with z,z' >= 0, j != j'  =>  z = z' = 0 (norms equal, then
    # directions differ).  With (2) (each page simplex meets z=0 exactly in a C_i/D_i face) and (1) for the
    # row subcomplex this gives conv(S) & conv(T) = conv(S & T) for simplices of different pages.
    analytic = circ and page_ok
    msg = 'unit-circle points exact & distinct & s_j>=0: %s; analytic reduction (z=0 lemma + checks 1,2): %s' % (
        circ, analytic)
    if not direct:
        return analytic, msg + '; direct R^4 LP check: not run (r or k > %d)' % DIRECT_R4_MAX, [], 0
    tagged = []
    for j in range(k):
        tagged += [(tuple(sorted(t)), j) for _, t in column_triangles(j, r)]
    tagged += [(tuple(sorted(t)), None) for _, t in row_triangles(r)]
    owner = dict(tagged)
    T = [t for t, _ in tagged]
    P4 = {}
    consistent = True
    for t, j in tagged:
        for v in t:
            if v[0] == 'C':
                imgs = {phi(jj, model_coord(v, r)) for jj in range(k)}
                consistent &= len(imgs) == 1
                P4[v] = imgs.pop()
            else:
                assert v[1] == j
                P4[v] = phi(j, model_coord(v, r))
    distinct = len(set(P4.values())) == len(P4)
    nondeg = all(aff_indep(t, P4) for t in T)
    cross = lambda S, U: owner[S] is not None and owner[U] is not None and owner[S] != owner[U]
    t0 = time.time()
    ncross, nlpc, badc = check_pairs(T, P4, cross)
    nall, nlpa, bada = check_pairs(T, P4, lambda S, U: not cross(S, U))
    ok = circ and consistent and distinct and nondeg and not badc and not bada and analytic
    msg += ('; direct R^4: %d vertices distinct: %s, %d triangles non-degenerate: %s, binding vertices '
            'page-independent: %s, %d cross-page triangle pairs proper: %s, plus %d same-page/binding '
            'triangle pairs proper in R^4: %s [%d exact LPs, %.1fs]'
            % (len(P4), distinct, len(T), nondeg, consistent, ncross, not badc, nall, not bada,
               nlpc + nlpa, time.time() - t0))
    return ok, msg, [(show(S, P4), show(U, P4)) for S, U in (badc + bada)[:10]], len(badc) + len(bada)


def negative_controls():
    """Deliberately broken coordinates: the checks must FAIL on each (shows they are not vacuous)."""
    global ROW_SHRINK, ROW_Z, CIRCLE
    saved = (ROW_SHRINK, ROW_Z, CIRCLE)
    out = []
    try:
        ROW_Z = Fr(1)
        pr = page_check(1)
        out.append(('C_i placed inside the seal plane z=1 (r=1): coplanar overlaps, (1)+(2) must fail',
                    not pr['1'][0] and not pr['2'][0], pr['1'][3]))
        ROW_Z = saved[1]
        ROW_SHRINK = Fr(3, 2)
        pr = page_check(2)
        out.append(('row shrink 3/2 instead of 1/2 (r=2): neighbouring frustums / D_i overlap, (1) must fail',
                    not pr['1'][0], pr['1'][3]))
        ROW_SHRINK = saved[0]
        CIRCLE = [saved[2][0], saved[2][0]]
        ok4, _, _, nbad = r4_check(1, 2, True, True)
        out.append(('two pages with the same direction (r=1,k=2): direct R^4 check must fail',
                    not ok4 and nbad > 0, nbad))
    finally:
        ROW_SHRINK, ROW_Z, CIRCLE = saved
    return out


# ============================================================================= paper scheme, general P
# The coordinates stated in paper/easy.tex, Section "The hard universes embed in R^4": paragraph "One
# column." + Lemma lem:column, paragraph "The open book" + Theorem thm:r4(i), for ARBITRARY admissible sets
# P in [r] x [k].  (The dense model above is an older variant: C_i = h_i shrunk about its centroid, P_j
# likewise, unit-circle page directions.  The text places C_i, P_j via eta_u and uses phi_j = (x,y,z,jz).)
DELTA = [(Fr(0), Fr(1)), (Fr(1), Fr(1)), (HALF, Fr(2))]   # delta_u as (y, z)
ETA = [(Fr(0), Fr(0)), (Fr(0), Fr(1)), (Fr(1), Fr(0))]    # eta_u as (x, y)
KNOB = {'row_scale': HALF, 'tether_z': HALF, 'reverse': False, 'slope': Fr}   # changed only by controls


def col_rows(P, j):
    return sorted(i for i, jj in P if jj == j)


def paper_column(rows, r, j):
    """Column j with admissible rows `rows` = P_{*j} = (i_1 < ... < i_d), placed in R^3 as in the text:
    s_{t,u} = (t, delta_u), (P_j)_(u) = (eta_u/2, 1/2), (C_i)_(u) = ((i,0) + eta_u/2, 0) for all i in [r],
    cone apexes (-1,1/2,3/2), (d+2,1/2,3/2).  Returns (coords, W, holes): W = triangles of the complex W
    of Lemma lem:column (all six triangles of Cyl(s_t,s_{t+1}) for 0<=t<=d -- so W contains the seal of
    h_0 --, the two cones, Cyl(h_0,P_j), Cyl(h_t,C_{i_t}) for t in [d], and E_j).  W'_j = W - {h_0}."""
    d = len(rows)
    X = {}
    s = [[('s', j, t, u) for u in range(3)] for t in range(d + 2)]
    for t in range(d + 2):
        for u in range(3):
            X[s[t][u]] = (Fr(t), DELTA[u][0], DELTA[u][1])
    Pj = [('P', j, u) for u in range(3)]
    for u in range(3):
        X[Pj[u]] = (HALF * ETA[u][0], HALF * ETA[u][1], KNOB['tether_z'])
    for i in range(1, r + 1):
        for u in range(3):
            X[('C', i, u)] = (i + KNOB['row_scale'] * ETA[u][0], KNOB['row_scale'] * ETA[u][1], Fr(0))
    A0, A1 = ('A', j, 0), ('A', j, 1)
    X[A0], X[A1] = (Fr(-1), HALF, Fr(3, 2)), (Fr(d + 2), HALF, Fr(3, 2))
    holes = [(s[t][0], s[t][1], s[t + 1][0]) for t in range(d + 1)]
    W = []
    for t in range(d + 1):
        W += cyl(s[t], s[t + 1])
    for u in range(3):
        W.append((A0, s[0][u], s[0][(u + 1) % 3]))
        W.append((A1, s[d + 1][u], s[d + 1][(u + 1) % 3]))
    W += cyl(holes[0], Pj)
    tgt = rows[::-1] if KNOB['reverse'] else rows
    for t in range(1, d + 1):
        W += cyl(holes[t], [('C', tgt[t - 1], u) for u in range(3)])
    W.append(tuple(Pj))
    return X, W, holes


def d_tris(r):
    return [tuple(('C', i, u) for u in range(3)) for i in range(1, r + 1)]


def page_key(X, W):
    """Page up to renaming the column index of the private vertices (to show it depends only on r, rows)."""
    st = lambda v: v if v[0] == 'C' else (v[0],) + v[2:]
    return frozenset((st(v), p) for v, p in X.items()), frozenset(frozenset(map(st, t)) for t in W)


def paper_page(r, rows):
    """(1) W (incl. seal of h_0) + all row cycles C_i and fillings D_i, i in [r]: all simplex pairs proper.
    (2) |W| & {z=0} = union of |C_{i_t}|, t in [d], and W lies in {z>=0}.  (T) claims of the text's proof."""
    X, W, holes = paper_column(list(rows), r, 1)
    d = len(rows)
    V, E, T = closure(W + d_tris(r))
    pts = [X[v[0]] for v in V]
    distinct = len(set(pts)) == len(pts)
    nondeg = all(aff_indep(x, X) for x in E + T)
    npairs, nlp, bad = check_pairs(V + E + T, X)
    res = {'1': (distinct and nondeg and not bad, (len(V), len(E), len(T), npairs, nlp),
                 [(show(S, X), show(U, X)) for S, U in bad[:6]], len(bad))}
    Vw, Ew, Tw = closure(W)
    sw = Vw + Ew + Tw
    expected = set()
    for i in rows:
        C = tuple(sorted(('C', i, u) for u in range(3)))
        expected.update((v,) for v in C)
        expected.update(itertools.combinations(C, 2))
    zpos = all(X[v[0]][2] >= 0 for v in Vw)
    inside = {x for x in sw if all(X[v][2] == 0 for v in x)}
    touch = [x for x in sw if any(X[v][2] == 0 for v in x)
             and tuple(v for v in x if X[v][2] == 0) not in expected]
    res['2'] = (zpos and inside == expected and not touch, len(inside), [show(x, X) for x in touch[:6]])
    tc = []
    for t in range(d + 1):      # hole vertices are ((t,0)+eta_u, 1)
        tc.append([X[v] for v in holes[t]] == [(t + ETA[u][0], ETA[u][1], Fr(1)) for u in range(3)])
    for z in (Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)):
        for t in range(1, d + 1):   # eq:section: z (h_t)_(u) + (1-z) (C_{i_t})_(u) = (1+z)/2 eta_u + (x_t(z),0)
            it = rows[t - 1]
            xt = z * t + (1 - z) * it
            for u in range(3):
                q = tuple(z * a + (1 - z) * b for a, b in zip(X[holes[t][u]], X[('C', it, u)]))
                tc.append(q == ((1 + z) / 2 * ETA[u][0] + xt, (1 + z) / 2 * ETA[u][1], z))
        if z >= HALF:               # section of F_0 at height z in [1/2,1] is z Delta'
            lam = 2 * z - 1
            for u in range(3):
                q = tuple(lam * a + (1 - lam) * b for a, b in zip(X[holes[0][u]], X[('P', 1, u)]))
                tc.append(q == (z * ETA[u][0], z * ETA[u][1], z))
    for t in range(d + 1):          # prism rectangles and frustum trapezoids are planar quads
        other = [('P', 1, u) for u in range(3)] if t == 0 else [('C', rows[t - 1], u) for u in range(3)]
        for qq in (cyl([('s', 1, t, u) for u in range(3)], [('s', 1, t + 1, u) for u in range(3)]),
                   cyl(list(holes[t]), other)):
            tc += [coplanar([X[v] for v in set(qq[2 * q]) | set(qq[2 * q + 1])]) for q in range(3)]
    tc.append(all(p[2] >= HALF for v, p in X.items() if v[0] != 'C'))      # off-row vertices: z >= 1/2
    tc += [{X[('C', i, u)][0] for u in range(3)} == {i, i + HALF} for i in range(1, r + 1)]  # D_i: [i,i+1/2]
    tc.append({X[('P', 1, u)][0] for u in range(3)} == {0, HALF})                         # E_j: [0,1/2]
    res['T'] = (all(tc), len(tc))
    res['key'] = page_key(X, W)
    return res


def universe(P, r, k):
    """U(P) per Definition def:gadget (paper/equiv.tex), built from the definition's own blocks
    (punctured cylinder with hole (a_0,a_1,b_0), seal, tube), independently of paper_column."""
    T, cycles = [], []
    for i in range(1, r + 1):
        C = tuple(('C', i, u) for u in range(3))
        cycles.append(C)
        T.append(C)                                                      # D_i
    for j in range(1, k + 1):
        rows = col_rows(P, j)
        d = len(rows)
        Pj = tuple(('P', j, u) for u in range(3))
        cycles.append(Pj)
        T.append(Pj)                                                     # E_j
        s = [tuple(('s', j, t, u) for u in range(3)) for t in range(d + 2)]
        cycles += s
        for o, a in ((('A', j, 0), s[0]), (('A', j, 1), s[d + 1])):     # cones on s_0, s_{d+1}
            T += [(o, a[u], a[(u + 1) % 3]) for u in range(3)]
        for t in range(d + 1):                                           # sockets
            a, b = s[t], s[t + 1]
            h = (a[0], a[1], b[0])
            T += [x for x in cyl(a, b) if set(x) != set(h)]              # Cyl°(a,b): 5 triangles
            if t == 0:
                T += cyl(h, Pj)                                          # hole tubed to the tether
            else:
                T.append(h)                                              # seal ...
                T += cyl(h, tuple(('C', rows[t - 1], u) for u in range(3)))   # ... and tube to C_{i_t}
    V = {v for x in T for v in x} | {v for c in cycles for v in c}
    E = {frozenset(e) for x in T for e in itertools.combinations(x, 2)}
    E |= {frozenset((c[u], c[(u + 1) % 3])) for c in cycles for u in range(3)}
    return T, V, E


def paper_triangles(r, k, P):
    """Triangles of X = union of W'_j (column j) and the D_i (owner 0), as sorted label tuples."""
    out, coords = [], []
    for j in range(1, k + 1):
        X, W, holes = paper_column(col_rows(P, j), r, j)
        coords.append((j, X))
        out += [(tuple(sorted(t)), j) for t in W if set(t) != set(holes[0])]
    out += [(tuple(sorted(t)), 0) for t in d_tris(r)]
    return out, coords


def paper_counts(r, k, P):
    """(4) realized triangle set == U(P) (set equality + counts)."""
    Tu, Vu, Eu = universe(P, r, k)
    geo = [t for t, _ in paper_triangles(r, k, P)[0]]
    Vg, Eg, Tg = closure(geo)
    n = len(P)
    su, sg = {frozenset(t) for t in Tu}, {frozenset(t) for t in geo}
    ok = (len(su) == len(Tu) and len(sg) == len(geo) and su == sg
          and len(Tu) == 12 * n + 18 * k + r and len(Vu) == 3 * r + 3 * n + 11 * k
          and len(Eu) == 3 * r + 15 * n + 27 * k and {v[0] for v in Vg} == Vu
          and {frozenset(e) for e in Eg} == Eu and len(Vu) - len(Eu) + len(Tu) == r + 2 * k)
    return ok, (len(Vu), len(Eu), len(Tu))


def paper_phi(j, p):
    return (p[0], p[1], p[2], KNOB['slope'](j) * p[2])     # phi_j(x,y,z) = (x,y,z,jz), j in [k]


def phi_algebra(k):
    """Exact: phi_j injective, = identity onto B on {z=0}; for j != j' the solutions of phi_j(p)=phi_j'(q)
    are exactly p = q in {z=0} (rank [M_j | -M_j'] = 4 and (e_x,e_x), (e_y,e_y) in the kernel)."""
    e = [(Fr(1), Fr(0), Fr(0)), (Fr(0), Fr(1), Fr(0)), (Fr(0), Fr(0), Fr(1))]
    M = {j: [paper_phi(j, v) for v in e] for j in range(1, k + 1)}       # columns phi_j(e_x,e_y,e_z)
    ok = all(rank_of(M[j]) == 3 and M[j][0] == (1, 0, 0, 0) and M[j][1] == (0, 1, 0, 0) for j in M)
    for j, jj in itertools.combinations(M, 2):
        cols = M[j] + [tuple(-a for a in c) for c in M[jj]]              # 6 columns in R^4
        ok &= rank_of(cols) == 4 and M[j][0] == M[jj][0] and M[j][1] == M[jj][1]
    return ok


def paper_assembly(r, k, P, direct):
    """(3) Full R^4 assembly X: exact direct check of all cross-page triangle pairs (and all other
    triangle pairs) when `direct`; returns (ok, info, bad list)."""
    tagged, coords = paper_triangles(r, k, P)
    owner = dict(tagged)
    tris = [t for t, _ in tagged]
    P4, consistent = {}, True
    for j, X in coords:
        for v, p in X.items():
            q = paper_phi(j, p)
            if v[0] == 'C':
                consistent &= P4.setdefault(v, q) == q
            else:
                P4[v] = q
    used = {v for t in tris for v in t}
    P4 = {v: P4[v] for v in used}
    distinct = len(set(P4.values())) == len(P4)
    nondeg = all(aff_indep(t, P4) for t in tris)
    if not direct:
        return consistent and distinct and nondeg, (len(P4), len(tris), 0, 0, 0), []
    cross = lambda S, U: owner[S] != 0 and owner[U] != 0 and owner[S] != owner[U]
    nc, nl1, badc = check_pairs(tris, P4, cross)
    no, nl2, bado = check_pairs(tris, P4, lambda S, U: not cross(S, U))
    ok = consistent and distinct and nondeg and not badc and not bado
    return ok, (len(P4), len(tris), nc, no, nl1 + nl2), [(show(S, P4), show(U, P4)) for S, U in (badc + bado)[:6]]


def paper_controls():
    """Deliberately broken variants of the paper scheme: the checks must FAIL on each."""
    out = []
    saved = dict(KNOB)
    try:
        KNOB['reverse'] = True
        pr = paper_page(2, (1, 2))
        out.append(('tubes attached in reversed row order (rows {1,2}): crossing frustums, (1) must fail',
                    not pr['1'][0], pr['1'][3]))
        KNOB.update(saved)
        KNOB['tether_z'] = Fr(0)
        pr = paper_page(1, (1,))
        out.append(('tether P_j moved into the binding z=0 (rows {1}): (2) must fail', not pr['2'][0],
                    len(pr['2'][2])))
        KNOB.update(saved)
        KNOB['slope'] = lambda j: Fr(1)
        ok, _, bad = paper_assembly(1, 2, {(1, 1), (1, 2)}, True)
        out.append(('all pages with the same slope (r=1,k=2,P=[1]x[2]): direct R^4 check must fail',
                    not ok and bool(bad), len(bad)))
    finally:
        KNOB.clear()
        KNOB.update(saved)
    return out


def fmtP(r, k, P):
    return 'r=%d k=%d cols=%s' % (r, k, '|'.join(''.join(map(str, col_rows(P, j))) or '-' for j in range(1, k + 1)))


def paper_main():
    t0 = time.time()
    all_ok = True
    print('==== paper scheme (paper/easy.tex: lem:column, thm:r4), general admissible P ====')
    print('    s_{t,u}=(t,delta_u), delta=(0,1),(1,1),(1/2,2); (P_j)_(u)=(eta_u/2,1/2); (C_i)_(u)=((i,0)+eta_u/2,0), '
          'eta=(0,0),(0,1),(1,0); apexes (-1,1/2,3/2),(d+2,1/2,3/2); phi_j(x,y,z)=(x,y,z,jz), j in [k]')
    for desc, detected, nbad in paper_controls():
        print('(P0) negative control -- %s: %s (%d bad)' % (desc, 'DETECTED' if detected else 'NOT DETECTED', nbad))
        all_ok &= detected
    # (1), (2), (T): every page that can occur for r <= 4 (all row sets S of [r]) -- exhaustive
    pages = {}
    for r in range(1, 5):
        tr = time.time()
        agg = [0, 0, 0, 0]
        for m in range(1 << r):
            rows = tuple(i for i in range(1, r + 1) if m >> (i - 1) & 1)
            pr = pages[(r, rows)] = paper_page(r, rows)
            agg[0] += pr['1'][1][3]
            agg[1] += pr['1'][1][4]
            agg[2] += pr['2'][1]
            agg[3] += pr['T'][1]
            for x in pr['1'][2]:
                print('      IMPROPER (r=%d rows=%s):' % (r, rows), x[0], 'vs', x[1])
            for x in pr['2'][2]:
                print('      BAD z=0 TOUCH (r=%d rows=%s):' % (r, rows), x)
        sub = [v for (rr, _), v in pages.items() if rr == r]
        ok1 = all(p['1'][0] for p in sub)
        ok2 = all(p['2'][0] for p in sub)
        okT = all(p['T'][0] for p in sub)
        print('[paper r=%d] all %d row sets S of [r]: (1) W_j (+seal h_0) + all C_i, D_i proper: %s [%d simplex '
              'pairs, %d exact LPs]; (2) |W| in {z>=0}, |W| & {z=0} = U_{i in S}|C_i| (%d simplices in z=0): %s; '
              'text claims (holes, eq:section, F_0 section, planar quads, heights, x-ranges; %d facts): %s [%.1fs]'
              % (r, len(sub), 'PASS' if ok1 else 'FAIL', agg[0], agg[1], agg[2], 'PASS' if ok2 else 'FAIL',
                 agg[3], 'PASS' if okT else 'FAIL', time.time() - tr))
        all_ok &= ok1 and ok2 and okT
    # random sparse P (r, k <= 4): page lookup (depends only on r and the row set), analytic R^4 argument, (4)
    rng = random.Random(20261102)
    Ps = [(4, 4, {(1, 2), (2, 2), (3, 2), (4, 2), (3, 3), (1, 4), (4, 4)}),   # empty, full, single, pair
          (4, 3, {(2, 2), (2, 3), (4, 3)}),                                  # rows 1, 3 unused, col 1 empty
          (3, 4, set()), (1, 1, {(1, 1)}), (1, 3, {(1, 2)})]
    while len(Ps) < 24:
        r, k = rng.randint(1, 4), rng.randint(1, 4)
        dens = rng.choice((0.15, 0.3, 0.5, 0.7, 0.9))
        Ps.append((r, k, {(i, j) for i in range(1, r + 1) for j in range(1, k + 1) if rng.random() < dens}))
    cov = {'empty col': 0, 'full col': 0, 'single-entry col': 0, 'unused row': 0}
    alg_ok = True
    for r, k, P in Ps:
        okp = True
        for j in range(1, k + 1):
            rows = tuple(col_rows(P, j))
            X, W, _ = paper_column(list(rows), r, j)
            pr = pages[(r, rows)]
            okp &= page_key(X, W) == pr['key'] and pr['1'][0] and pr['2'][0] and pr['T'][0]
            cov['empty col'] += not rows
            cov['full col'] += len(rows) == r
            cov['single-entry col'] += len(rows) == 1
        cov['unused row'] += sum(1 for i in range(1, r + 1) if all((i, j) not in P for j in range(1, k + 1)))
        alg = phi_algebra(k)
        alg_ok &= alg
        oka, _, _ = paper_assembly(r, k, P, False)
        ok4, (nv, ne, nt) = paper_counts(r, k, P)
        print('[paper %s] (1)+(2) pages (looked up by row set, identical up to column relabeling): %s; (3) analytic '
              '(phi_j algebra exact: %s; vertices injective, binding vertices page-independent: %s): %s; (4) X == U(P): '
              '%s (V=%d E=%d T=%d)' % (fmtP(r, k, P), 'PASS' if okp else 'FAIL', alg, oka,
                                        'PASS' if okp and alg and oka else 'FAIL', 'PASS' if ok4 else 'FAIL', nv, ne, nt))
        all_ok &= okp and alg and oka and ok4
    covok = all(v > 0 for v in cov.values()) and len(Ps) >= 15
    print('[paper] random P: %d instances; coverage %s: %s' % (len(Ps), cov, 'PASS' if covok else 'FAIL'))
    all_ok &= covok
    # (3) direct exact R^4 check of the full assembly, r, k <= 3
    Qs = [(3, 3, {(i, j) for i in range(1, 4) for j in range(1, 4)}), (2, 3, set()),
          (3, 3, {(1, 1), (3, 1), (1, 2), (2, 2), (2, 3), (3, 3)})]
    while len(Qs) < 8:
        r, k = rng.randint(1, 3), rng.randint(2, 3)
        dens = rng.choice((0.3, 0.5, 0.7))
        Qs.append((r, k, {(i, j) for i in range(1, r + 1) for j in range(1, k + 1) if rng.random() < dens}))
    for r, k, P in Qs:
        td = time.time()
        ok, (nv, nt, nc, no, nlp), bad = paper_assembly(r, k, P, True)
        ok4, _ = paper_counts(r, k, P)
        okan = phi_algebra(k) and all(pages[(r, tuple(col_rows(P, j)))]['1'][0] and
                                      pages[(r, tuple(col_rows(P, j)))]['2'][0] for j in range(1, k + 1))
        print('[paper %s] (3) direct R^4: %d vertices distinct, %d triangles non-degenerate, %d cross-page triangle '
              'pairs + %d same-page/binding pairs proper: %s [%d exact LPs, %.1fs]; analytic: %s; (4) X == U(P): %s'
              % (fmtP(r, k, P), nv, nt, nc, no, 'PASS' if ok else 'FAIL', nlp, time.time() - td,
                 'PASS' if okan else 'FAIL', 'PASS' if ok4 else 'FAIL'))
        for x in bad:
            print('      IMPROPER (R^4):', x[0], 'vs', x[1])
        all_ok &= ok and ok4 and okan
    print('[paper] analytic R^4 argument: images of distinct pages meet exactly in B (exact linear algebra), each page '
          'meets B exactly in its row cycles (2), pages and binding are complexes (1) => Lemma glue; total %.1fs'
          % (time.time() - t0))
    return all_ok


def main():
    t_start = time.time()
    all_ok = True
    st_ok, nst = self_test()
    print('(0) checker self-test (%d known proper/improper configs in R^3 and R^4, incl. coplanar): %s'
          % (nst, 'PASS' if st_ok else 'FAIL'))
    all_ok &= st_ok
    for desc, detected, nbad in negative_controls():
        print('(0) negative control -- %s: %s (%d improper pairs found)'
              % (desc, 'DETECTED' if detected else 'NOT DETECTED', nbad))
        all_ok &= detected
    print('    construction: s_m=((m,0,1),(m,1,1),(m,1/2,2)); apexes (-1,1/2,3/2),(r+2,1/2,3/2); '
          'C_i = h_i shrunk by %s at z=%s; P_j = h_0 shrunk by %s at z=%s; pages (c_j,s_j) = %s'
          % (ROW_SHRINK, ROW_Z, TETHER_SHRINK, TETHER_Z, ', '.join('(%s,%s)' % cs for cs in CIRCLE)))
    page_cache = {}
    for r, k in CASES:
        if k > len(CIRCLE):
            raise ValueError('not enough page directions')
        if r not in page_cache:
            page_cache[r] = page_check(r)
        pr = page_cache[r]
        pfx = '[r=%d,k=%d]' % (r, k)
        ok1, m1, b1, _ = pr['1']
        print('%s (1) page = geometric simplicial complex: %s -- %s' % (pfx, 'PASS' if ok1 else 'FAIL', m1))
        for x in b1:
            print('      IMPROPER:', x[0], 'vs', x[1])
        ok2, m2, b2 = pr['2']
        print('%s (2) page meets z=0 exactly in C_i boundaries + D_i: %s -- %s' % (pfx, 'PASS' if ok2 else 'FAIL', m2))
        for x in b2:
            print('      BAD TOUCH:', x)
        ok3, m3 = counts_check(r, k)
        ok3 = ok3 and pr['3geo']
        print('%s (3) realized triangles = combinatorial triangles: %s -- %s; coordinates match description '
              '(holes, planar prism quads, planar frustum faces, heights): %s'
              % (pfx, 'PASS' if ok3 else 'FAIL', m3, pr['3geo']))
        direct = r <= DIRECT_R4_MAX and k <= DIRECT_R4_MAX
        ok4, m4, b4, _ = r4_check(r, k, ok1 and ok2, direct)
        print('%s (4) cross-page R^4 assembly: %s -- %s' % (pfx, 'PASS' if ok4 else 'FAIL', m4))
        for x in b4:
            print('      IMPROPER (R^4):', x[0], 'vs', x[1])
        all_ok &= ok1 and ok2 and ok3 and ok4
    all_ok &= paper_main()
    print('total time %.1fs' % (time.time() - t_start))
    print('ALL VALIDATED:', bool(all_ok))
    return 0 if all_ok else 1


if __name__ == '__main__':
    sys.exit(main())
