"""threshold.py -- Remark rem:threshold: for A with entries in {-1,0,1} and at most two nonzeros per column,
rank_F A[R,J] = |R| - c(double cover) + c(Gamma), with half-edges at inactive rows (F = F_2, F_3, F_5)."""
import random

def fp_rank(rows, p):
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

def comps(nodes, edges):
    par = {v: v for v in nodes}
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for a, b in edges: par[f(a)] = f(b)
    return len({f(v) for v in nodes})

rng = random.Random(3); ok = tot = 0
for trial in range(600):
    r, k = rng.randint(1, 6), rng.randint(1, 6); p = rng.choice([2, 3, 5])
    A = [[0] * k for _ in range(r)]
    for j in range(k):
        for i in rng.sample(range(r), rng.randint(0, min(2, r))): A[i][j] = rng.choice([1, -1])
    R = {i for i in range(r) if rng.random() < .7}; J = {j for j in range(k) if rng.random() < .7}
    sub = [{jj: A[i][j] for jj, j in enumerate(sorted(J)) if A[i][j]} for i in sorted(R)]
    rank = fp_rank(sub, p) if sub else 0
    G, H = [], []
    for j in J:
        nz = [i for i in range(r) if A[i][j]]
        if len(nz) == 2:
            a, b = nz; pos = (p == 2) or (A[a][j] != A[b][j])
            G.append((a, b))
            H += [((a, 1), (b, 1)), ((a, -1), (b, -1))] if pos else [((a, 1), (b, -1)), ((a, -1), (b, 1))]
        elif len(nz) == 1:
            a = nz[0]; G.append((a, a)); H.append(((a, 1), (a, -1)))
    for i in range(r):
        if i not in R: G.append((i, i)); H.append(((i, 1), (i, -1)))
    formula = len(R) - comps([(i, s) for i in range(r) for s in (1, -1)], H) + comps(list(range(r)), G)
    tot += 1; ok += (rank == formula)
print(f"threshold formula rank A[R,J] = |R| - c(double cover) + c(Gamma): {ok}/{tot}")
print("ALL VALIDATED:", ok == tot)
