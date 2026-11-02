"""signed.py -- the reversed tube for entries -1 (equiv.tex, after Cor. switch-only): for A with entries in {0,1,-1},
entry 1 tubes the hole h to C_i = (c0,c1,c2), entry -1 tubes h to the reversed cycle (c0,c2,c1), entry 0 seals h.
Checks over F_3 and F_5 (oriented boundary): dim Z_2(K(A;R,J)) = |J| - rank_F A[R,J]; flip costs O(1) triangles."""
import random
from itertools import combinations

def cylinder(a, b):
    m = len(a)
    return ([(a[i], a[(i + 1) % m], b[i]) for i in range(m)]
            + [(a[(i + 1) % m], b[i], b[(i + 1) % m]) for i in range(m)])

def disk(a, ctr):
    return [(ctr, a[i], a[(i + 1) % len(a)]) for i in range(len(a))]

def fp_rank_rows(rows, p):
    rows = [dict(r) for r in rows]; piv = {}; rk = 0
    for r in rows:
        r = {c: v % p for c, v in r.items() if v % p}
        while r:
            j = max(r)
            if j in piv:
                pr = piv[j]; mult = (r[j] * pow(pr[j], -1, p)) % p
                r = {c: (r.get(c, 0) - mult * pr.get(c, 0)) % p for c in set(r) | set(pr)}
                r = {c: v for c, v in r.items() if v}
            else:
                piv[j] = r; rk += 1; break
    return rk

def oriented_z2_dim(tris, p):
    """dim ker d_2 over F_p for triangles given as vertex tuples (orientation of a triangle irrelevant for the kernel dim)."""
    tris = [tuple(sorted(t)) for t in set(frozenset(t) for t in tris)]
    eidx = {}
    rows = []
    for (a, b, c) in tris:
        col = {}
        for (u, v), s in (((b, c), 1), ((a, c), -1), ((a, b), 1)):
            e = eidx.setdefault((u, v), len(eidx)); col[e] = s
        rows.append(col)
    return len(tris) - fp_rank_rows(rows, p)

def matrix_rank_fp(A, p):
    return fp_rank_rows([{j: x for j, x in enumerate(row) if x % p} for row in A], p) if A and A[0] else 0

class B:
    def __init__(s): s.V = 0; s.T = []
    def fresh(s, n): xs = list(range(s.V, s.V + n)); s.V += n; return xs

def build(A, r, k, R, J):
    b = B(); C = [b.fresh(3) for _ in range(r)]
    for i in range(r):
        if i not in R: b.T.append(tuple(C[i]))                     # kill switch: fill C_i
    for j in range(k):
        s = b.fresh(3); b.T += disk(s, b.fresh(1)[0])
        P = b.fresh(3); s2 = b.fresh(3)
        cyl = cylinder(s, s2); h = (s[0], s[1], s2[0])
        b.T += [t for t in cyl if set(t) != set(h)] + cylinder(list(h), P)   # tether socket
        if j in J: b.T.append(tuple(P))                              # activation: fill P_j
        s = s2
        for i in range(r):
            s2 = b.fresh(3); cyl = cylinder(s, s2); h = (s[0], s[1], s2[0])
            b.T += [t for t in cyl if set(t) != set(h)]
            x = A[i][j]
            if x == 0: b.T.append(h)
            elif x == 1: b.T += cylinder(list(h), C[i])
            else: b.T += cylinder(list(h), [C[i][0], C[i][2], C[i][1]])  # reversed tube
            s = s2
        b.T += disk(s, b.fresh(1)[0])
    return b.T

rng = random.Random(7); ok = tot = 0; diff_fields = 0; flips = set()
for trial in range(120):
    r, k = rng.randint(1, 4), rng.randint(1, 4)
    A = [[rng.choice([0, 1, -1]) for _ in range(k)] for _ in range(r)]
    R = {i for i in range(r) if rng.random() < .7}; J = {j for j in range(k) if rng.random() < .7}
    T = build(A, r, k, R, J)
    sub = [[A[i][j] for j in sorted(J)] for i in sorted(R)]
    for p in (3, 5):
        tot += 1
        ok += oriented_z2_dim(T, p) == len(J) - (matrix_rank_fp(sub, p) if sub and sub[0] else 0)
    if sub and sub[0] and matrix_rank_fp(sub, 3) != matrix_rank_fp([[abs(x) for x in row] for row in sub], 3): diff_fields += 1
    i, j = rng.randrange(r), rng.randrange(k)
    for newx in (0, 1, -1):
        if newx != A[i][j]:
            A2 = [row[:] for row in A]; A2[i][j] = newx
            flips.add(len(set(map(frozenset, T)) ^ set(map(frozenset, build(A2, r, k, R, J)))))
print(f"signed crux over F3/F5: {ok}/{tot}; instances where the signed rank differs from the 0/1 rank of |A|: {diff_fields}; triangle changes per entry update: {sorted(flips)}")
print("ALL VALIDATED:", ok == tot)
