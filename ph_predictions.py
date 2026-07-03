"""
ph_predictions.py
=================
Independent computational validation for "Dynamic Persistent Homology is Rank-Complete".

Anti-fabrication harness: each NEW claim in the paper is cross-checked against an
independent brute-force ground truth. If any assertion in run_tests() fails, there is a
bug in the code OR the theory -- either way we must know before claiming it.

Validated here:
  L1  (Lemma 1, decomposition):  H_M has a directed cycle  <=>  some pair-digraph D_p does.
  C2  (Corollary 2):             every D_p has out-degree <= p+1 and girth >= 3 (no 2-cycle).
  T1  (Theorem 1/2, repair=DFVS): min pairs to delete to make M acyclic (direct brute force)
                                  equals  eta(M) = sum_p dfvs(D_p).
  T3  (Theorem 3, graphs):       for 1-complexes, D_0 is functional (out-deg<=1) and
                                  dfvs(D_0) = number of vertex-disjoint directed cycles.
  COR (Prop 1 / Mischaikow-Nanda): Betti(Morse complex of any certified matching) = Betti(K),
                                  and Euler characteristic is preserved.
  GAD (Theorem 6 gadget):        the tetra-minus-a-face gadget has a directed 3-cycle in D_1,
                                  dfvs = 1, out-degrees <= 2, girth 3.

Pure Python 3, no dependencies.
"""

from __future__ import annotations
import itertools, random
from collections import defaultdict


# ------------------------------- simplicial complexes ---------------------------------

def faces(simplex):
    if len(simplex) <= 1:
        return []
    return [simplex - frozenset([v]) for v in simplex]


def closure(simplices):
    out = set()
    stack = [frozenset(s) for s in simplices]
    while stack:
        s = stack.pop()
        if s in out or len(s) == 0:
            continue
        out.add(s)
        for f in faces(s):
            if f not in out:
                stack.append(f)
    return out


def vietoris_rips(points, radius, maxdim):
    n = len(points)
    r2 = radius * radius
    def d2(i, j):
        return sum((a - b) ** 2 for a, b in zip(points[i], points[j]))
    adj = {i: set() for i in range(n)}
    for i in range(n):
        for j in range(i + 1, n):
            if d2(i, j) <= r2:
                adj[i].add(j); adj[j].add(i)
    simplices = set(frozenset([i]) for i in range(n))
    current = [frozenset([i]) for i in range(n)]
    for _size in range(2, maxdim + 2):
        nxt = []
        for clq in current:
            common = set.intersection(*[adj[v] for v in clq]) if clq else set()
            for v in common:
                if all(v > u for u in clq):
                    newc = clq | frozenset([v])
                    simplices.add(newc); nxt.append(newc)
        current = nxt
    return closure(simplices)


def by_dim(simplices):
    d = defaultdict(list)
    for s in simplices:
        d[len(s) - 1].append(s)
    for k in d:
        d[k].sort(key=lambda s: tuple(sorted(s)))
    return d


# ------------------------------- F2 linear algebra ------------------------------------

def f2_rank(columns):
    pivots = {}
    rank = 0
    for col in columns:
        c = set(col)
        while c:
            p = max(c)
            if p in pivots:
                c ^= pivots[p]
            else:
                pivots[p] = c; rank += 1; break
    return rank


def _boundary_columns(cells_lower, cells_upper):
    idx = {s: i for i, s in enumerate(cells_lower)}
    cols = []
    for u in cells_upper:
        cols.append(set(idx[f] for f in faces(u) if f in idx))
    return cols


def betti_numbers(simplices, maxdim=None):
    D = by_dim(simplices)
    if maxdim is None:
        maxdim = max(D.keys()) if D else 0
    rank = {}
    for p in range(0, maxdim + 2):
        lower, upper = D.get(p - 1, []), D.get(p, [])
        rank[p] = f2_rank(_boundary_columns(lower, upper)) if upper and lower else 0
    betti = {}
    for p in range(0, maxdim + 1):
        betti[p] = (len(D.get(p, [])) - rank.get(p, 0)) - rank.get(p + 1, 0)
    while maxdim > 0 and betti.get(maxdim, 0) == 0:
        del betti[maxdim]; maxdim -= 1
    return betti


def euler_char(simplices):
    D = by_dim(simplices)
    return sum(((-1) ** p) * len(v) for p, v in D.items())


# ------------------------------- discrete Morse matchings -----------------------------

def is_matching(matching):
    seen = set()
    for lo, up in matching:
        if len(up) - len(lo) != 1 or not (lo < up):
            return False
        if lo in seen or up in seen:
            return False
        seen.add(lo); seen.add(up)
    return True


def modified_hasse_cycle(simplices, matching):
    """Direct ground truth: does H_M have a directed cycle? (tau->sigma down; sigma->tau matched)."""
    matched_pairs = set((lo, up) for lo, up in matching)
    S = set(simplices)
    adj = defaultdict(list)
    for s in S:
        for f in faces(s):
            if f in S:
                if (f, s) in matched_pairs:
                    adj[f].append(s)
                else:
                    adj[s].append(f)
    color = defaultdict(int)  # 0 white,1 gray,2 black
    def dfs(u):
        color[u] = 1
        for v in adj[u]:
            if color[v] == 1: return True
            if color[v] == 0 and dfs(v): return True
        color[u] = 2; return False
    for s in S:
        if color[s] == 0 and dfs(s):
            return True
    return False


def pair_digraph(matching, p):
    nodes = [(lo, up) for (lo, up) in matching if len(lo) - 1 == p]
    by_lower = {lo: (lo, up) for (lo, up) in nodes}
    adj = {nd: [] for nd in nodes}
    for (lo, up) in nodes:
        for fac in faces(up):
            if fac != lo and fac in by_lower:
                adj[(lo, up)].append(by_lower[fac])
    return nodes, adj


def digraph_has_cycle(nodes, adj):
    color = {nd: 0 for nd in nodes}
    def dfs(u):
        color[u] = 1
        for v in adj[u]:
            if color[v] == 1: return True
            if color[v] == 0 and dfs(v): return True
        color[u] = 2; return False
    return any(color[nd] == 0 and dfs(nd) for nd in nodes)


def matching_acyclic_via_pairdigraphs(matching):
    dims = set(len(lo) - 1 for lo, _ in matching)
    return all(not digraph_has_cycle(*pair_digraph(matching, p)) for p in dims)


def min_dfvs_bruteforce(nodes, adj):
    if not digraph_has_cycle(nodes, adj):
        return 0
    nodes = list(nodes)
    for k in range(1, len(nodes) + 1):
        for sub in itertools.combinations(nodes, k):
            ss = set(sub)
            rem = [nd for nd in nodes if nd not in ss]
            adj2 = {nd: [v for v in adj[nd] if v not in ss] for nd in rem}
            if not digraph_has_cycle(rem, adj2):
                return k
    return len(nodes)


def eta_via_pairdigraphs(matching):
    dims = set(len(lo) - 1 for lo, _ in matching)
    return sum(min_dfvs_bruteforce(*pair_digraph(matching, p)) for p in dims)


def min_dfvs_set_bruteforce(nodes, adj):
    """Return an actual minimum directed feedback vertex SET (small instances)."""
    if not digraph_has_cycle(nodes, adj):
        return set()
    nodes = list(nodes)
    for k in range(1, len(nodes) + 1):
        for sub in itertools.combinations(nodes, k):
            ss = set(sub)
            rem = [nd for nd in nodes if nd not in ss]
            adj2 = {nd: [v for v in adj[nd] if v not in ss] for nd in rem}
            if not digraph_has_cycle(rem, adj2):
                return ss
    return set(nodes)


def exact_repair(matching):
    """Optimal MAS: delete a minimum feedback vertex set in each pair-digraph (Theorem 1).
       Keeps exactly |matching| - eta pairs."""
    dims = set(len(lo) - 1 for lo, _ in matching)
    remove = set()
    for p in dims:
        nodes, adj = pair_digraph(matching, p)
        remove |= min_dfvs_set_bruteforce(nodes, adj)
    return [pr for pr in matching if pr not in remove]


def min_pairs_to_acyclic_direct(simplices, matching):
    """Ground truth for Theorem 1: fewest pairs to DELETE so the matching is acyclic,
       checked with the DIRECT modified-Hasse cycle test (independent of pair-digraphs)."""
    if not modified_hasse_cycle(simplices, matching):
        return 0
    m = len(matching)
    for k in range(1, m + 1):
        for sub in itertools.combinations(range(m), k):
            ss = set(sub)
            keep = [matching[i] for i in range(m) if i not in ss]
            if not modified_hasse_cycle(simplices, keep):
                return k
    return m


def greedy_repair(matching):
    kept = []
    for pr in matching:
        if matching_acyclic_via_pairdigraphs(kept + [pr]):
            kept.append(pr)
    return kept


# ------------------------------- Morse complex (gradient flow) ------------------------

def morse_complex_homology(simplices, matching):
    """Betti numbers of the Morse complex of an ACYCLIC matching, via the flow projection pi.
       pi(sigma) = critical part of the gradient flow of sigma (F2 set of critical cells):
         sigma critical            -> {sigma}
         sigma matched-lower to tau -> XOR over facets of tau (except sigma) of pi(.)
         sigma matched-upper        -> {}   (projected out)
       Acyclicity guarantees the recursion terminates."""
    S = set(simplices)
    matched_up = {lo: up for lo, up in matching}      # lower -> coface
    matched_dn = {up: lo for lo, up in matching}      # upper -> face
    crit = set(s for s in S if s not in matched_up and s not in matched_dn)

    memo = {}
    def pi(sigma):
        if sigma in memo:
            return memo[sigma]
        memo[sigma] = set()  # guard (acyclic => not actually needed, but safe)
        if sigma in crit:
            res = {sigma}
        elif sigma in matched_up:
            tau = matched_up[sigma]
            res = set()
            for f in faces(tau):
                if f in S and f != sigma:
                    res ^= pi(f)
        else:  # matched-upper
            res = set()
        memo[sigma] = res
        return res

    crit_by_dim = defaultdict(list)
    for c in crit:
        crit_by_dim[len(c) - 1].append(c)

    # Morse boundary of critical c (dim p+1): pi applied to ordinary boundary
    def dM(c):
        out = set()
        for f in faces(c):
            if f in S:
                out ^= pi(f)
        return out

    maxdim = max(crit_by_dim.keys()) if crit_by_dim else 0
    rank = {}
    for p in range(0, maxdim + 2):
        lower = crit_by_dim.get(p - 1, [])
        upper = crit_by_dim.get(p, [])
        idx = {s: i for i, s in enumerate(lower)}
        cols = [set(idx[g] for g in dM(u) if g in idx) for u in upper]
        rank[p] = f2_rank(cols) if cols and lower else 0
    betti = {}
    for p in range(0, maxdim + 1):
        betti[p] = (len(crit_by_dim.get(p, [])) - rank.get(p, 0)) - rank.get(p + 1, 0)
    while maxdim > 0 and betti.get(maxdim, 0) == 0:
        del betti[maxdim]; maxdim -= 1
    return betti, {p: len(v) for p, v in crit_by_dim.items()}


# ------------------------------- random predictions -----------------------------------

def random_matching(simplices, density, rng):
    S = list(simplices); rng.shuffle(S)
    used, matching = set(), []
    Sset = set(simplices)
    for up in S:
        if up in used or len(up) == 0:
            continue
        fcs = [f for f in faces(up) if f in Sset and f not in used]
        rng.shuffle(fcs)
        if fcs and rng.random() < density:
            lo = fcs[0]
            matching.append((lo, up)); used.add(lo); used.add(up)
    return matching


# ------------------------------- the Theorem-6 gadget ---------------------------------

def gadget_complex():
    """Tetra abcd minus face acd: triangles abc,bcd,abd (+faces). Vertices 0=a,1=b,2=c,3=d."""
    a, b, c, d = 0, 1, 2, 3
    tris = [frozenset([a, b, c]), frozenset([b, c, d]), frozenset([a, b, d])]
    K = closure(tris)
    # matching {(ab,abc),(bc,bcd),(bd,abd)} -- the directed 3-cycle of Thm 6
    M = [(frozenset([a, b]), frozenset([a, b, c])),
         (frozenset([b, c]), frozenset([b, c, d])),
         (frozenset([b, d]), frozenset([a, b, d]))]
    return K, M


def test_gadget():
    K, M = gadget_complex()
    assert is_matching(M)
    assert modified_hasse_cycle(K, M), "gadget should be cyclic"
    nodes, adj = pair_digraph(M, p=1)
    assert len(nodes) == 3
    # it is a single directed 3-cycle
    assert all(len(adj[u]) == 1 for u in nodes), f"out-degrees {[len(adj[u]) for u in nodes]}"
    assert digraph_has_cycle(nodes, adj)
    # no 2-cycle (girth 3)
    for u in nodes:
        for v in adj[u]:
            assert u not in adj[v], "found a 2-cycle (violates Cor 2)"
    assert min_dfvs_bruteforce(nodes, adj) == 1, "dfvs of a 3-cycle must be 1"
    assert min_pairs_to_acyclic_direct(K, M) == 1
    print("  [GAD] tetra-minus-face gadget: directed 3-cycle in D_1, dfvs=1, girth 3  OK")


def test_graphs(seed, trials):
    """Theorem 3: for 1-complexes D_0 is functional and dfvs = #disjoint cycles."""
    rng = random.Random(seed)
    for _ in range(trials):
        n = rng.randint(4, 8)
        edges = set()
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < 0.5:
                    edges.add(frozenset([i, j]))
        K = closure(edges | set(frozenset([i]) for i in range(n)))
        M = random_matching(K, density=0.9, rng=rng)
        nodes, adj = pair_digraph(M, p=0)
        assert all(len(adj[u]) <= 1 for u in nodes), "D_0 not functional!"
        # functional-graph dfvs = number of (vertex-disjoint) directed cycles
        # count cycles by following successors
        succ = {u: (adj[u][0] if adj[u] else None) for u in nodes}
        seen, oncyc = set(), 0
        for start in nodes:
            if start in seen:
                continue
            path, u = [], start
            local = {}
            while u is not None and u not in seen:
                if u in local:           # found a fresh cycle
                    oncyc += 1
                    break
                local[u] = len(path); path.append(u); u = succ[u]
            for x in path:
                seen.add(x)
        assert min_dfvs_bruteforce(nodes, adj) == oncyc, "Thm3: dfvs != #cycles"
    print(f"  [T3] graphs: D_0 functional & dfvs=#cycles on {trials} random graphs  OK")


# ------------------------------- main cross-check loop --------------------------------

def run_tests(seed=0, trials=150):
    rng = random.Random(seed)
    checked = needed_repair = l1 = t1 = 0
    max_outdeg_seen = defaultdict(int)
    for _ in range(trials):
        amb = rng.choice([2, 3])
        npts = rng.randint(5, 8)
        pts = [tuple(rng.random() for _ in range(amb)) for _ in range(npts)]
        K = vietoris_rips(pts, rng.uniform(0.55, 0.95), maxdim=rng.choice([2, 3]))
        if len(K) < 4:
            continue
        M = random_matching(K, density=rng.uniform(0.4, 0.95), rng=rng)
        assert is_matching(M)
        if len(M) > 13:        # keep brute force feasible
            M = M[:13]
            if not is_matching(M):
                continue

        # L1: decomposition
        direct_cyclic = modified_hasse_cycle(K, M)
        pd_acyclic = matching_acyclic_via_pairdigraphs(M)
        assert direct_cyclic == (not pd_acyclic), "L1 FAILED"
        l1 += 1
        if direct_cyclic:
            needed_repair += 1

        # C2: out-degree <= p+1 and girth >= 3 in every D_p
        for p in set(len(lo) - 1 for lo, _ in M):
            nodes, adj = pair_digraph(M, p)
            for u in nodes:
                assert len(adj[u]) <= p + 1, f"C2 out-degree {len(adj[u])} > {p+1}"
                max_outdeg_seen[p] = max(max_outdeg_seen[p], len(adj[u]))
                for v in adj[u]:
                    assert u not in adj[v], "C2 girth: found a 2-cycle"

        # T1: repair size two independent ways
        direct_min = min_pairs_to_acyclic_direct(K, M)
        eta = eta_via_pairdigraphs(M)
        assert direct_min == eta, f"T1 FAILED: direct {direct_min} != eta {eta}"
        t1 += 1

        # COR: certified matching reproduces homology + Euler characteristic
        Mr = greedy_repair(M)
        assert not modified_hasse_cycle(K, Mr)
        mbetti, crit_counts = morse_complex_homology(K, Mr)
        assert mbetti == betti_numbers(K), f"COR FAILED: {mbetti} != {betti_numbers(K)}"
        chi_morse = sum(((-1) ** p) * c for p, c in crit_counts.items())
        assert chi_morse == euler_char(K), "Euler characteristic not preserved"
        assert greedy_repair(Mr) == Mr, "greedy not idempotent on acyclic input"
        checked += 1

    print(f"[run_tests seed={seed}] checked={checked}  needed_repair={needed_repair}")
    print(f"   L1 verified on {l1};  T1 (repair=DFVS) verified on {t1};  "
          f"max out-degree by dim {dict(max_outdeg_seen)}")
    return checked


if __name__ == "__main__":
    print("=== gadget & graph specializations ===")
    test_gadget()
    test_graphs(seed=1, trials=300)
    print("=== randomized end-to-end cross-checks (VR complexes, dim 2-3) ===")
    total = sum(run_tests(seed=s, trials=120) for s in range(5))
    print(f"\nTOTAL instances cross-checked: {total}")
    print("If you see this line with no AssertionError above, every checked claim held.")
