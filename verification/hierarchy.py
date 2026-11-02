"""Check of Theorem thm:hier, Lemma lem:merge and Corollary cor:treewidth (Section 6.3).

Not part of any proof.  For random sparse matrices over F_p we maintain the
summaries (r_theta, W_theta) of Lemma lem:merge along random column hierarchies
under random column switches and compare r_root with a direct rank computation
after every switch.  For random matrices whose row/column graph comes with a
tree decomposition of width t, we build the column hierarchy of the proof of
Corollary cor:treewidth and check that every node has |Bd| <= Delta*(t+1).
Standard library only.
"""
import random

def rank_mod(vectors, p):
    """Rank over F_p of a list of dict vectors {row: value}."""
    rows = [dict(v) for v in vectors if v]
    rk, pivots = 0, {}
    for v in rows:
        v = {k: x % p for k, x in v.items() if x % p}
        while v:
            k = min(v)
            if k in pivots:
                pv = pivots[k]; f = v[k] * pow(pv[k], p - 2, p) % p
                for kk, xx in pv.items():
                    v[kk] = (v.get(kk, 0) - f * xx) % p
                    if v[kk] == 0: del v[kk]
            else:
                pivots[k] = v; rk += 1; break
    return rk

def echelon(vectors, order, p):
    """Row-reduce dict vectors; coordinates compared by position in `order`."""
    pos = {c: i for i, c in enumerate(order)}
    basis = []  # list of (lead, vec)
    for v in vectors:
        v = {k: x % p for k, x in v.items() if x % p}
        changed = True
        while v and changed:
            changed = False
            lead = min(v, key=lambda c: pos[c])
            for (l, b) in basis:
                if l == lead:
                    f = v[lead] * pow(b[lead], p - 2, p) % p
                    for kk, xx in b.items():
                        v[kk] = (v.get(kk, 0) - f * xx) % p
                        if v[kk] == 0: del v[kk]
                    changed = True; break
        if v:
            lead = min(v, key=lambda c: pos[c]); basis.append((lead, v))
    return basis

class Node:
    def __init__(self, leaf=None, kids=()):
        self.leaf, self.kids, self.parent = leaf, list(kids), None
        for c in self.kids: c.parent = self

def leaves(node):
    return [node.leaf] if node.leaf is not None else [x for c in node.kids for x in leaves(c)]

def setup(root, cols_of_row):
    """Compute L, In, Bd, X for every node (two children per inner node)."""
    nodes = []
    def walk(n):
        nodes.append(n)
        for c in n.kids: walk(c)
    walk(root)
    for n in nodes:
        L = set(leaves(n)); n.L = L
        n.In = {i for i, cs in cols_of_row.items() if cs <= L}
        n.Bd = {i for i, cs in cols_of_row.items() if cs & L and not cs <= L}
    for n in nodes:
        if n.kids:
            a, b = n.kids
            n.X = n.In - (a.In | b.In)
            assert n.X <= (a.Bd & b.Bd)                      # Lemma merge (a)
            assert (a.Bd | b.Bd) == (n.Bd | n.X) and not (n.Bd & n.X)   # (b)
    return nodes

def compute(n, M, J, p):
    """Summary (r, basis of W restricted to Bd) of node n, from its children."""
    if n.leaf is not None:
        j = n.leaf
        if j not in J: return 0, []
        col = M[j]
        if any(col.get(i, 0) % p for i in n.In): return 1, []
        return 0, [dict(col)]
    (ra, Wa), (rb, Wb) = n.kids[0].summ, n.kids[1].summ
    order = sorted(n.X) + sorted(n.Bd)
    basis = echelon(Wa + Wb, order, p)
    inX = [v for (l, v) in basis if l in n.X]
    rest = [v for (l, v) in basis if l not in n.X]
    for v in rest: assert all(k in n.Bd for k in v)
    return ra + rb + len(inX), rest

def random_hierarchy(cols):
    cols = list(cols); random.shuffle(cols)
    def build(cs):
        if len(cs) == 1: return Node(leaf=cs[0])
        s = random.randint(1, len(cs) - 1)
        return Node(kids=[build(cs[:s]), build(cs[s:])])
    return build(cols)

def run_dynamic(M, cols_of_row, root, p, steps):
    nodes = setup(root, cols_of_row)
    width = max(len(n.Bd) for n in nodes)
    J = set()
    for n in reversed(nodes): n.summ = compute(n, M, J, p)
    leaf_of = {n.leaf: n for n in nodes if n.leaf is not None}
    ks = list(leaf_of)
    for _ in range(steps):
        j = random.choice(ks); J ^= {j}
        n = leaf_of[j]
        while n is not None:
            n.summ = compute(n, M, J, p); n = n.parent
        direct = rank_mod([M[c] for c in J], p)
        if root.summ[0] != direct: return False, width
    return True, width

def random_matrix(r, k, density, p):
    M = {j: {} for j in range(k)}
    for j in range(k):
        for i in range(r):
            if random.random() < density: M[j][i] = random.randint(1, p - 1)
        if not M[j]: M[j][random.randrange(r)] = 1
    return M

def rows_map(M):
    cor = {}
    for j, col in M.items():
        for i in col: cor.setdefault(i, set()).add(j)
    return cor

def treewidth_instance(nT, nr, nc, t, Delta, p):
    """Random tree T, random connected subtrees T_v, bags of size <= t+1."""
    par = [None] + [random.randrange(i) for i in range(1, nT)]
    adj = {u: [] for u in range(nT)}
    for u in range(1, nT): adj[u].append(par[u]); adj[par[u]].append(u)
    load = [0] * nT
    def subtree(size):
        cand = [u for u in range(nT) if load[u] < t + 1]
        if not cand: return None
        S = {random.choice(cand)}
        for _ in range(size - 1):
            fr = [w for u in S for w in adj[u] if w not in S and load[w] < t + 1]
            if not fr: break
            S.add(random.choice(fr))
        for u in S: load[u] += 1
        return S
    Trow = {i: subtree(random.randint(1, 3)) for i in range(nr)}
    Tcol = {j: subtree(random.randint(1, 3)) for j in range(nc)}
    Trow = {i: S for i, S in Trow.items() if S}; Tcol = {j: S for j, S in Tcol.items() if S}
    M = {}
    for j, Sj in Tcol.items():
        nb = [i for i, Si in Trow.items() if Si & Sj]
        random.shuffle(nb)
        chosen = nb[:random.randint(1, Delta)] if nb else []
        if chosen: M[j] = {i: random.randint(1, p - 1) for i in chosen}
    bags = {u: set() for u in range(nT)}
    for i, S in Trow.items():
        for u in S: bags[u].add(('r', i))
    for j, S in Tcol.items():
        if j in M:
            for u in S: bags[u].add(('c', j))
    tw = max(len(b) for b in bags.values()) - 1
    return par, Tcol, M, bags, tw

def hierarchy_from_decomposition(par, Tcol, M, nT):
    depth = [0] * nT
    for u in range(1, nT): depth[u] = depth[par[u]] + 1
    home = {j: min(Tcol[j], key=lambda u: depth[u]) for j in M}
    kids = {u: [] for u in range(nT)}
    for u in range(1, nT): kids[par[u]].append(u)
    A = {u: [] for u in range(nT)}
    for j, h in home.items(): A[h].append(j)
    def balanced(items):
        if len(items) == 1: return items[0]
        m = len(items) // 2
        return Node(kids=[balanced(items[:m]), balanced(items[m:])])
    def build(u):
        pieces = [x for x in (build(c) for c in kids[u]) if x is not None]
        pieces += [Node(leaf=j) for j in A[u]]
        return balanced(pieces) if pieces else None
    return build(0)

def main():
    random.seed(20261102)
    ok = True; tests = 0
    for p in (2, 3, 5, 7):
        for _ in range(60):
            r, k = random.randint(1, 9), random.randint(1, 9)
            M = random_matrix(r, k, random.choice((0.2, 0.35, 0.6)), p)
            good, _ = run_dynamic(M, rows_map(M), random_hierarchy(range(k)), p, 40)
            ok &= good; tests += 1
    print('random hierarchies over F_2, F_3, F_5, F_7:', tests, 'instances, 40 switches each, all correct:', ok)
    tw_ok = True; tw_tests = 0
    for p in (2, 3):
        for _ in range(150):
            t, Delta = random.randint(1, 4), random.randint(1, 3)
            par, Tcol, M, bags, tw = treewidth_instance(random.randint(2, 12), random.randint(2, 14), random.randint(2, 14), t, Delta, p)
            if not M: continue
            root = hierarchy_from_decomposition(par, Tcol, M, len(par))
            cor = rows_map(M)
            nodes = setup(root, cor)
            assert sorted(leaves(root)) == sorted(M)
            width = max(len(n.Bd) for n in nodes)
            tw_ok &= width <= Delta * (tw + 1)
            good, _ = run_dynamic(M, cor, root, p, 30)
            tw_ok &= good; tw_tests += 1
    print('tree-decomposition hierarchies:', tw_tests, 'instances, width <= Delta*(t+1) and dynamic rank correct:', tw_ok)
    print('ALL VALIDATED:', ok and tw_ok)

if __name__ == '__main__':
    main()
