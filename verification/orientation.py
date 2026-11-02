"""orientation.py -- checks the explicit orientation argument of Section 3 (proof that all signs in the boundary
formula of a column surface agree): d Cyl(a,b) = [a]-[b], d Cyl°(a,b) = [a]-[b]-[h], d Cyl(h,c) = [h]-[c], the cone
orientations, the column identity d[Sigma_j] = -[P_j] - sum_{A_ij=1} [C_i], and coherence (every interior edge lies in
exactly two triangles inducing opposite orientations)."""
# Verify the explicit orientation argument of Section 3: d Cyl(a,b) = [a]-[b], d Cyl°(a,b) = [a]-[b]-[h],
# d Cyl(h,c) = [h]-[c], cones, and the column sum d[Sigma_j] = -[P_j] - sum A_ij [C_i], coherent orientation.
from collections import defaultdict
import random
def bd(tri):  # oriented triangle (x,y,z) -> dict of oriented edges with signs
    x, y, z = tri; out = defaultdict(int)
    for (u, v) in ((x, y), (y, z), (z, x)):
        if u < v: out[(u, v)] += 1
        else: out[(v, u)] -= 1
    return out
def add(D, E, s=1):
    for k, v in E.items(): D[k] += s * v
    return D
def cyc(x):  # [x] = x0x1 + x1x2 + x2x0
    D = defaultdict(int)
    for (u, v) in ((x[0], x[1]), (x[1], x[2]), (x[2], x[0])):
        if u < v: D[(u, v)] += 1
        else: D[(v, u)] -= 1
    return D
def cyl(a, b): return [(a[t], a[(t+1)%3], b[t]) for t in range(3)] + [(a[(t+1)%3], b[(t+1)%3], b[t]) for t in range(3)]
def chain_bd(tris):
    D = defaultdict(int)
    for t in tris: add(D, bd(t))
    return {k: v for k, v in D.items() if v}
def eq(D1, D2):
    keys = set(D1) | set(D2)
    return all(D1.get(k, 0) == D2.get(k, 0) for k in keys)
def lin(*terms):
    D = defaultdict(int)
    for s, x in terms: add(D, x, s)
    return {k: v for k, v in D.items() if v}
ok = True; V = iter(range(10**6))
fresh = lambda n: [next(V) for _ in range(n)]
for _ in range(50):
    rng = random.Random(_)
    a, b, c = fresh(3), fresh(3), fresh(3)
    C = cyl(a, b); h = (a[0], a[1], b[0])
    ok &= eq(chain_bd(C), lin((1, cyc(a)), (-1, cyc(b))))
    P = [t for t in C if t != h]
    ok &= eq(chain_bd(P), lin((1, cyc(a)), (-1, cyc(b)), (-1, cyc(h))))
    ok &= eq(chain_bd(cyl(list(h), c)), lin((1, cyc(h)), (-1, cyc(c))))
    # whole column: cone(s0) neg, tether socket, d sockets, cone(s_last) pos
    d = rng.randint(1, 5); bits = [rng.randint(0, 1) for _ in range(d)]
    Pj = fresh(3); rows = [fresh(3) for _ in range(d)]
    s = [fresh(3) for _ in range(d + 2)]
    o1, o2 = next(V), next(V)
    tris = [(o1, s[0][(t+1)%3], s[0][t]) for t in range(3)]
    def socket(x, y, tgt, bit):
        cc = cyl(x, y); hh = (x[0], x[1], y[0]); base = [t for t in cc if t != hh]
        return base + ([hh] if bit == 0 else cyl(list(hh), tgt))
    tris += socket(s[0], s[1], Pj, 1)
    for t in range(d): tris += socket(s[t+1], s[t+2], rows[t], bits[t])
    tris += [(o2, s[d+1][t], s[d+1][(t+1)%3]) for t in range(3)]
    want = lin((-1, cyc(Pj)), *[(-1, cyc(rows[t])) for t in range(d) if bits[t]])
    ok &= eq(chain_bd(tris), want)
    # coherence: every edge not on Pj/rows appears in exactly two triangles with opposite induced signs
    inc = defaultdict(list)
    for t in tris:
        for k, v in bd(t).items(): inc[k].append(v)
    bnd = set(cyc(Pj)) | set().union(*[set(cyc(rows[t])) for t in range(d) if bits[t]])
    for k, vs in inc.items():
        if k in bnd: ok &= (len(vs) == 1)
        else: ok &= (len(vs) == 2 and vs[0] + vs[1] == 0)
print("orientation argument verified:", ok)
print("ALL VALIDATED:", ok)
