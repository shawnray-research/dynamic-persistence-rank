"""fields.py -- the gadget over fields of characteristic != 2.

Lemma (Crux) of the paper is stated over every field.  Over F_2 orientations play no role; over other fields
the proof needs all signs in the boundary formula of a column surface to agree.  This script builds the hole
gadget (same construction as hole_gadget.py), computes rank of the ORIENTED (signed) boundary matrix over
F_3 and F_5, and checks  dim Z_2 = k - rank(A)  and, for the switched complex,  dim Z_2 = |J| - rank A[R,J].
It includes matrices whose rank over F_3 would change if any sign pattern were non-uniform
(e.g. [[1,1],[1,1]] versus [[1,1],[1,-1]]).
"""
import os, random
_here = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(_here, 'hole_gadget.py')).read().split('\nrng = random.Random(5)')[0]
ns = {}; exec(_src, ns)
build = ns['build']

def rank_mod(rows, ncols, p):
    M = [r[:] for r in rows]; rk = 0; col = 0
    nr = len(M)
    for c in range(ncols):
        piv = None
        for i in range(rk, nr):
            if M[i][c] % p: piv = i; break
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [(x * inv) % p for x in M[rk]]
        for i in range(nr):
            if i != rk and M[i][c] % p:
                f = M[i][c]; M[i] = [(a - f * b) % p for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk

def z2_dim(tris, p):
    tris = [tuple(sorted(t)) for t in tris]
    edges = sorted({(t[a], t[b]) for t in tris for a, b in ((0,1),(0,2),(1,2))})
    eidx = {e: i for i, e in enumerate(edges)}
    # rows = triangles (transpose is fine for rank)
    rows = []
    for (x, y, z) in tris:
        row = [0] * len(edges)
        row[eidx[(y, z)]] += 1; row[eidx[(x, z)]] -= 1; row[eidx[(x, y)]] += 1
        rows.append([v % p for v in row])
    return len(tris) - rank_mod(rows, len(edges), p)

def mat_rank(A, p):
    if not A or not A[0]: return 0
    return rank_mod([[x % p for x in r] for r in A], len(A[0]), p)

rng = random.Random(11); ok = tot = 0
for trial in range(40):
    r, k = rng.randint(1, 4), rng.randint(1, 4)
    A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
    for p in (3, 5):
        b = build(A, r, k)
        tot += 1; ok += (z2_dim(b.tris, p) == k - mat_rank(A, p))
        u = {x for x in range(r) if rng.random() < .5}; v = {x for x in range(k) if rng.random() < .5}
        bs = build(A, r, k, u, v, switched=True)
        sub = [[A[x][y] for y in sorted(v)] for x in sorted(u)]
        tot += 1; ok += (z2_dim(bs.tris, p) == len(v) - mat_rank(sub, p))
# adversarial: matrices whose F3-rank differs under sign changes, e.g. [[1,1],[1,1]] vs signed
for A in ([[1,1],[1,1]], [[1,1,0],[0,1,1],[1,0,1]], [[1,1,1],[1,1,1],[1,1,1]], [[1,0,1,1],[0,1,1,1],[1,1,0,1]]):
    r, k = len(A), len(A[0])
    for p in (3, 5):
        b = build(A, r, k); tot += 1; ok += (z2_dim(b.tris, p) == k - mat_rank(A, p))
print(f"hole gadget over F3/F5 (signed boundaries): {ok}/{tot}")
print("ALL VALIDATED:", ok == tot)
