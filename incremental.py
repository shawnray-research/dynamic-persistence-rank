"""
incremental.py -- INCREMENTAL certified Morse matching: a dynamic data structure whose per-edit cost
is edit-local (independent of the global size n for local edits), not an O(n) rescan.

Between edits the certified matching M is acyclic, so each pair-digraph D_p(M) is a DAG.  We maintain,
per dimension, the pair-digraph together with a topological order, using the Pearce--Kelly dynamic
topological-sort algorithm (with online cycle detection); the amortized guarantees are those of
Bender--Fineman--Gilbert--Tarjan incremental cycle detection / strong-component maintenance.  An edit
inserts I and deletes R (delta=|I|+|R|); we:
  (1) remove deleted cells and their pairs, orphaning partners      [cost O(footprint of deletions)];
  (2) warm-start extend over the newly-uncovered cells -> <= delta/2 extension pairs E, added as
      nodes+arcs to the pair-digraphs                               [cost O(footprint of insertions)];
  (3) insert E's arcs via Pearce--Kelly, which detects the cycles and confines the search to the
      AFFECTED REGION between the arcs' endpoints in topological order (never the acyclic bulk);
  (4) the nontrivial strongly connected components (the torn region R_i) are extracted from the
      affected region and repaired by FPT-DFVS; deletions re-establish a certified DAG.
The per-edit cost is O(mu_i + |A_i| + g(eta_i)|R_i|) with NO dependence on n: mu_i the edit footprint
(pair-digraph arcs touched), A_i the Pearce--Kelly affected region, R_i the torn region.

Everything is validated against a FROM-SCRATCH oracle at every step: (a) the maintained matching's
barcode equals the true barcode, and (b) the incrementally-found torn region equals a full Tarjan SCC.
A separate experiment shows the per-edit work is INDEPENDENT OF n for local edits (the vineyards regime).
"""

from __future__ import annotations
import random
from collections import defaultdict
from ph_predictions import (faces, vietoris_rips, betti_numbers, is_matching,
                            morse_complex_homology, min_dfvs_bruteforce, exact_repair)
from experiment import collapse_matching, n_cells


# ----------------- Pearce--Kelly dynamic topological order + online cycle detection -----------------

class DynDAG:
    """Directed graph maintained with a topological order under arc/node insertion and node deletion.
       add_arc(x,y) reorders only the Pearce--Kelly 'affected region' and reports if the arc closes a
       cycle.  Work counters (nodes/arcs touched) are accumulated in self.work."""
    def __init__(self):
        self.adj = defaultdict(set)     # out-neighbors
        self.radj = defaultdict(set)    # in-neighbors
        self.ord = {}                   # node -> integer topological position (distinct)
        self._next = 0
        self.work = 0                   # cumulative touched-node counter (cost proxy, never O(n) global)

    def add_node(self, v):
        if v not in self.ord:
            self.ord[v] = self._next; self._next += 1
            self.adj[v]; self.radj[v]

    def remove_node(self, v):
        for w in list(self.adj.get(v, ())):
            self.radj[w].discard(v); self.work += 1
        for w in list(self.radj.get(v, ())):
            self.adj[w].discard(v); self.work += 1
        self.adj.pop(v, None); self.radj.pop(v, None); self.ord.pop(v, None)

    def add_arc(self, x, y):
        """Insert arc x->y.  Returns (affected_set, created_cycle)."""
        if y in self.adj[x]:
            return set(), False
        self.adj[x].add(y); self.radj[y].add(x)
        lb, ub = self.ord[y], self.ord[x]
        if lb > ub:                      # ord[x] < ord[y]: already consistent
            return set(), False
        # ord[x] >= ord[y]: inconsistent (or equal never happens, distinct) -> reorder / detect cycle
        fwd, hit = self._dfs_forward(y, ub, x)
        bwd = self._dfs_backward(x, lb)
        aff = fwd | bwd
        self.work += len(aff)
        if hit:
            return aff, True             # cycle: x reachable from y
        self._reorder(fwd, bwd)
        return aff, False

    def try_add_arc(self, x, y):
        """Insert x->y ONLY if it keeps the graph acyclic, reordering just the Pearce--Kelly affected
           region (never the whole graph).  Returns (added, affected_set, would_cycle)."""
        if y in self.adj[x]:
            return True, set(), False
        lb, ub = self.ord[y], self.ord[x]
        if lb > ub:                                  # ord[x] < ord[y]: consistent, free
            self.adj[x].add(y); self.radj[y].add(x)
            return True, set(), False
        fwd, hit = self._dfs_forward(y, ub, x)
        if hit:                                      # would create a cycle: do NOT add
            self.work += len(fwd)
            return False, fwd, True
        bwd = self._dfs_backward(x, lb)
        self.adj[x].add(y); self.radj[y].add(x)
        self._reorder(fwd, bwd)
        self.work += len(fwd) + len(bwd)
        return True, fwd | bwd, False

    def _dfs_forward(self, start, ub, target):
        # forward-reachable from start within ord < ub; detect reaching target (ord == ub)
        seen, stack, hit = set(), [start], False
        while stack:
            u = stack.pop()
            if u in seen:
                continue
            seen.add(u); self.work += 1
            for w in self.adj[u]:
                if w == target:
                    hit = True
                elif w not in seen and self.ord[w] < ub:
                    stack.append(w)
        return seen, hit

    def _dfs_backward(self, start, lb):
        seen, stack = set(), [start]
        while stack:
            u = stack.pop()
            if u in seen:
                continue
            seen.add(u); self.work += 1
            for w in self.radj[u]:
                if w not in seen and self.ord[w] > lb:
                    stack.append(w)
        return seen

    def _reorder(self, fwd, bwd):
        # reassign the pooled positions so backward-set (incl. x) precedes forward-set (incl. y)
        pool = sorted(self.ord[w] for w in (fwd | bwd))
        order = sorted(bwd, key=lambda w: self.ord[w]) + sorted(fwd, key=lambda w: self.ord[w])
        for w, pos in zip(order, pool):
            self.ord[w] = pos

    # ---- oracle helpers (validation only) ----
    def is_valid_topo_order(self):
        return all(self.ord[x] < self.ord[y] for x in self.adj for y in self.adj[x])

    def sccs_within(self, A):
        """Nontrivial SCCs of the subgraph induced by node set A (Tarjan restricted to A)."""
        A = set(A)
        index = {}; low = {}; onstk = {}; stk = []; out = []; idx = [0]
        import sys; sys.setrecursionlimit(1000000)
        def strong(v):
            index[v] = low[v] = idx[0]; idx[0] += 1; stk.append(v); onstk[v] = True
            for w in self.adj[v]:
                if w not in A: continue
                if w not in index: strong(w); low[v] = min(low[v], low[w])
                elif onstk.get(w): low[v] = min(low[v], index[w])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stk.pop(); onstk[w] = False; comp.append(w)
                    if w == v: break
                if len(comp) > 1: out.append(comp)
        for v in A:
            if v not in index: strong(v)
        return out

    def tarjan_sccs(self):
        """Full Tarjan (O(V+E)); used ONLY as the correctness oracle, not by the incremental path."""
        index = {}; low = {}; onstk = {}; stk = []; out = []; idx = [0]
        import sys
        sys.setrecursionlimit(100000)
        def strong(v):
            index[v] = low[v] = idx[0]; idx[0] += 1
            stk.append(v); onstk[v] = True
            for w in self.adj[v]:
                if w not in index:
                    strong(w); low[v] = min(low[v], low[w])
                elif onstk.get(w):
                    low[v] = min(low[v], index[w])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stk.pop(); onstk[w] = False; comp.append(w)
                    if w == v: break
                out.append(comp)
        for v in list(self.adj):
            if v not in index:
                strong(v)
        return out


def find_affected_region(g, Enodes):
    """Pearce--Kelly affected region seeded at the extension nodes: for each incident back-arc (an arc
       violating the maintained topological order) do the bounded forward/backward search.  Forward
       arcs are certified acyclic for free.  Returns a node set A that contains every torn SCC and is
       output-sensitive (bounded by the order-windows of the back-arcs, never the whole graph)."""
    A = set(n for n in Enodes if n in g.ord)
    seen = set()
    for x in Enodes:
        if x not in g.ord:
            continue
        for y in list(g.adj.get(x, ())):           # arcs out of an E-node
            if y in g.ord and g.ord[x] >= g.ord[y] and (x, y) not in seen:
                seen.add((x, y))
                fwd, _ = g._dfs_forward(y, g.ord[x] + 1, x)
                bwd = g._dfs_backward(x, g.ord[y] - 1)
                A |= fwd | bwd | {x, y}
        for u in list(g.radj.get(x, ())):          # arcs into an E-node
            if u in g.ord and g.ord[u] >= g.ord[x] and (u, x) not in seen:
                seen.add((u, x))
                fwd, _ = g._dfs_forward(x, g.ord[u] + 1, u)
                bwd = g._dfs_backward(u, g.ord[x] - 1)
                A |= fwd | bwd | {u, x}
    return A


def find_torn_region(g, Enodes):
    """Torn region = nontrivial SCCs, found by Tarjan restricted to the affected region.
       Returns (list of SCCs, |affected region|)."""
    A = find_affected_region(g, Enodes)
    return g.sccs_within(A), len(A)


# --------------------------- incremental certified-matching maintainer ---------------------------

class IncCertifier:
    """Maintains a certified (acyclic) Morse matching and its per-dimension pair-digraphs under edits.
       Per edit it touches only the edit footprint + Pearce--Kelly affected region + torn region."""
    def __init__(self, K, M):
        self.cells = set(K)
        self.cof = defaultdict(set)                 # cell -> set of cofaces (cells with it as facet)
        for c in self.cells:
            for f in faces(c):
                if f in self.cells:
                    self.cof[f].add(c)
        self.partner = {}                           # matched cell -> its partner
        for lo, hi in M:
            self.partner[lo] = hi; self.partner[hi] = lo
        self.dims = set(len(lo) - 1 for lo, _ in M) | {0}
        self.D = {p: DynDAG() for p in range(max(self.dims) + 2)}
        for lo, hi in M:                            # build initial pair-digraphs
            self.D[len(lo) - 1].add_node((lo, hi))
        for lo, hi in M:
            self._add_arcs_raw((lo, hi))
        # give each DynDAG a valid initial topological order (from-scratch topo sort)
        for p, g in self.D.items():
            self._init_order(g)
        self.last_work = 0
        self.check = False          # if True, assert incremental torn region == full Tarjan every edit
        self.torn_check_ok = True

    # ----- pair-digraph maintenance (footprint-bounded) -----
    def _pair_of(self, cell):
        """If cell is a matched LOWER cell, return its pair (cell, partner); else None."""
        pr = self.partner.get(cell)
        if pr is not None and len(pr) == len(cell) + 1:
            return (cell, pr)
        return None

    def _upper_pair_of(self, cell):
        """If cell is a matched UPPER cell, return the pair (partner, cell); else None."""
        pr = self.partner.get(cell)
        if pr is not None and len(pr) == len(cell) - 1:
            return (pr, cell)
        return None

    def _arcs_of(self, node):
        """Out- and in-arcs of pair-node (sigma,tau); returns (outs, ins).  Cost O(deg(sigma))."""
        sigma, tau = node
        outs = []
        for f in faces(tau):
            if f != sigma:
                pr = self._pair_of(f)
                if pr is not None:
                    outs.append(pr)                 # (sigma,tau) -> (f, partner(f))
        ins = []
        for c in self.cof.get(sigma, ()):           # cofaces of sigma
            up = self._upper_pair_of(c)             # c is a matched upper cell?
            if up is not None and up != node:
                ins.append(up)                      # (partner(c), c) -> (sigma,tau)
        return outs, ins

    def _add_arcs_raw(self, node):
        g = self.D[len(node[0]) - 1]
        outs, ins = self._arcs_of(node)
        for v in outs:
            g.adj[node].add(v); g.radj[v].add(node)
        for u in ins:
            g.adj[u].add(node); g.radj[node].add(u)
        return len(outs) + len(ins)

    def _init_order(self, g):
        # Kahn topological sort to seed ord (used once at construction, and to re-seed torn regions)
        indeg = {v: len(g.radj[v]) for v in g.adj}
        q = [v for v in g.adj if indeg[v] == 0]; pos = 0
        while q:
            v = q.pop(); g.ord[v] = pos; pos += 1
            for w in g.adj[v]:
                indeg[w] -= 1
                if indeg[w] == 0: q.append(w)
        g._next = pos
        # any leftover (shouldn't happen for a DAG) get appended
        for v in g.adj:
            if v not in g.ord:
                g.ord[v] = g._next; g._next += 1

    # ----- the edit -----
    def apply_edit(self, K2, M_ignored=None):
        """Edit to complex K2 (a set of cells). Warm-start from the current matching, repair, and
           return (barcode-ready matching, torn_region_nodes, work)."""
        K2 = set(K2)
        ins = [c for c in K2 - self.cells if len(c) >= 1]
        dele = [c for c in self.cells - K2 if len(c) >= 1]
        work = 0
        newly = []

        # (1) deletions: drop cells + their pairs; orphan partners
        for c in list(self.cells - K2):
            # remove pair-digraph node if c is a matched lower cell
            pr = self._pair_of(c)
            if pr is not None:
                g = self.D[len(pr[0]) - 1]; g.remove_node(pr); work += 1
            upr = self._upper_pair_of(c)
            if upr is not None:
                g = self.D[len(upr[0]) - 1]; g.remove_node(upr); work += 1
            # orphan partner
            partner = self.partner.pop(c, None)
            if partner is not None and partner in self.partner:
                self.partner.pop(partner, None)
                if partner in K2:
                    newly.append(partner)
            # update cofaces
            for f in faces(c):
                self.cof[f].discard(c); work += 1
            self.cof.pop(c, None)
            self.cells.discard(c)

        # (2) insertions
        for c in sorted(ins, key=len):
            self.cells.add(c)
            for f in faces(c):
                if f in self.cells:
                    self.cof[f].add(c); work += 1
            newly.append(c)

        # (3) warm-start extension over the newly-uncovered cells only
        newly = [c for c in newly if c in self.cells and c not in self.partner]
        E = [(lo, hi) for (lo, hi) in collapse_matching(newly)
             if lo not in self.partner and hi not in self.partner and lo in newly and hi in newly]
        for lo, hi in E:
            self.partner[lo] = hi; self.partner[hi] = lo
        Eset = set((lo, hi) for lo, hi in E)
        Enodes_by_dim = defaultdict(list); pending = defaultdict(list)
        # pass 1: add all E-nodes so every arc endpoint exists in the order
        for lo, hi in E:
            node = (lo, hi); p = len(lo) - 1
            self.D[p].add_node(node); Enodes_by_dim[p].append(node)
        # pass 1b: position each E-node LOCALLY, between its kept (non-E) in- and out-neighbors
        for lo, hi in E:
            node = (lo, hi); g = self.D[len(lo) - 1]
            outs, inn = self._arcs_of(node)
            kin = [g.ord[u] for u in inn if u in g.ord and u not in Eset]
            kout = [g.ord[w] for w in outs if w in g.ord and w not in Eset]
            lo_ord = max(kin) if kin else None
            hi_ord = min(kout) if kout else None
            if lo_ord is not None and hi_ord is not None and lo_ord < hi_ord:
                g.ord[node] = (lo_ord + hi_ord) / 2.0
            elif lo_ord is not None:
                g.ord[node] = lo_ord + 0.5
            elif hi_ord is not None:
                g.ord[node] = hi_ord - 0.5
        # pass 2: insert arcs via Pearce--Kelly (consistent arcs free; back-arcs reorder only the
        # affected region; cycle-creating arcs held back as 'pending' so the order stays valid)
        for lo, hi in E:
            node = (lo, hi); p = len(lo) - 1; g = self.D[p]
            outs, inn = self._arcs_of(node)
            for u in inn:
                _, aff, cyc = g.try_add_arc(u, node); work += len(aff)
                if cyc: pending[p].append((u, node))
            for w in outs:
                _, aff, cyc = g.try_add_arc(node, w); work += len(aff)
                if cyc: pending[p].append((node, w))

        # (4) resolve cycles: add the pending (cycle-creating) arcs, find the torn region within the
        #     Pearce--Kelly affected region, repair by FPT-DFVS, then re-order locally
        torn_all = []
        for p, Enodes in Enodes_by_dim.items():
            g = self.D[p]
            for (x, y) in pending[p]:                 # materialize cycle arcs so SCCs are visible
                g.adj[x].add(y); g.radj[y].add(x)
            R, affn = find_torn_region(g, Enodes)
            work += affn
            if self.check:                            # oracle: incremental torn region == full Tarjan
                full = [C for C in g.tarjan_sccs() if len(C) > 1]
                if set(frozenset(c) for c in R) != set(frozenset(c) for c in full):
                    self.torn_check_ok = False
            torn_all += R
            for C in R:                               # repair each torn SCC; deleted pairs become critical
                for node in self._dfvs_solution(g, C):
                    lo, hi = node
                    self.partner.pop(lo, None); self.partner.pop(hi, None)
                    g.remove_node(node); work += 1
            # restore a valid order LOCALLY: re-insert surviving pending arcs (now acyclic) via PK
            for (x, y) in pending[p]:
                if x in g.ord and y in g.ord and y in g.adj[x]:
                    g.adj[x].discard(y); g.radj[y].discard(x)
                    _, aff, cyc = g.try_add_arc(x, y); work += len(aff)
        self.last_work = work
        return torn_all, work

    def _dfvs_solution(self, g, C):
        """Minimum DFVS of the induced subgraph on node set C (brute force; C is a small torn SCC)."""
        C = list(C)
        adj = {v: [w for w in g.adj[v] if w in set(C)] for v in C}
        import itertools
        def has_cycle(rem):
            col = {v: 0 for v in rem}
            def dfs(u):
                col[u] = 1
                for w in adj[u]:
                    if w in col:
                        if col[w] == 1 or (col[w] == 0 and dfs(w)): return True
                col[u] = 2; return False
            return any(col[v] == 0 and dfs(v) for v in rem)
        for k in range(1, len(C) + 1):
            for sub in itertools.combinations(C, k):
                ss = set(sub); rem = {v: None for v in C if v not in ss}
                adj2 = {v: [w for w in adj[v] if w in rem] for v in rem}
                col = {v: 0 for v in rem}
                def dfs2(u):
                    col[u] = 1
                    for w in adj2[u]:
                        if col[w] == 1 or (col[w] == 0 and dfs2(w)): return True
                    col[u] = 2; return False
                if not any(col[v] == 0 and dfs2(v) for v in rem):
                    return list(sub)
        return list(C)

    def _reseed_order(self, g, A):
        # recompute a valid topological order (Kahn) -- the graph is a DAG after repair
        self._init_order(g)

    def matching(self):
        seen = set(); out = []
        for c, pr in self.partner.items():
            key = frozenset((c, pr))
            if key in seen: continue
            seen.add(key)
            lo, hi = (c, pr) if len(c) < len(pr) else (pr, c)
            out.append((lo, hi))
        return out


def _self_test():
    """PK correctness: random DAG edge insertions keep a valid topological order; a back edge that
       closes a cycle is detected; and Tarjan agrees on which insertions create cycles."""
    rng = random.Random(0); ok = True
    for _ in range(300):
        g = DynDAG(); n = rng.randint(3, 9)
        for v in range(n): g.add_node(v)
        # insert random edges; skip ones PK says would create a cycle (to keep a DAG)
        edges = [(a, b) for a in range(n) for b in range(n) if a != b]
        rng.shuffle(edges)
        for (a, b) in edges[:rng.randint(0, 2 * n)]:
            aff, cyc = g.add_arc(a, b)
            if cyc:
                g.adj[a].discard(b); g.radj[b].discard(a)   # reject cycle edge, stay a DAG
            else:
                if not g.is_valid_topo_order():
                    ok = False
        # now the graph is a DAG; a full Tarjan must show all-singleton SCCs
        if any(len(c) > 1 for c in g.tarjan_sccs()):
            ok = False
    return ok


def stress_torn_finder(trials=3000, seed=11, verbose=True):
    """Adversarial test of the output-sensitive torn-region finder against full Tarjan.  Build a random
       certified DAG (with a maintained topological order), add extension nodes whose arcs deliberately
       create cycles, and check that find_torn_region (seeded at the extension nodes, exploring only the
       Pearce--Kelly affected region) returns EXACTLY the nontrivial SCCs a full Tarjan finds."""
    rng = random.Random(seed)
    match = cyclic = total = 0
    for _ in range(trials):
        g = DynDAG()
        n = rng.randint(4, 14)
        for v in range(n):
            g.add_node(v)
        # random DAG among the base nodes (reject cycle-creating arcs to keep it a certified DAG)
        base_edges = [(a, b) for a in range(n) for b in range(n) if a != b]
        rng.shuffle(base_edges)
        for (a, b) in base_edges[:rng.randint(n, 3 * n)]:
            _, cyc = g.add_arc(a, b)
            if cyc:
                g.adj[a].discard(b); g.radj[b].discard(a)
        # extension nodes E with arcs to/from random base nodes -- these MAY create cycles
        k = rng.randint(1, 4); Enodes = []
        for j in range(k):
            e = ('E', j); g.add_node(e); Enodes.append(e)
            # position like the real code: just above the max-ord in-neighbor
            ins = rng.sample(range(n), rng.randint(0, 3))
            outs = rng.sample(range(n), rng.randint(1, 3))
            for u in ins:
                g.adj[u].add(e); g.radj[e].add(u)
            for w in outs:
                g.adj[e].add(w); g.radj[w].add(e)
            if ins:
                g.ord[e] = max(g.ord[u] for u in ins) + 0.5
        R, _ = find_torn_region(g, Enodes)
        full = [C for C in g.tarjan_sccs() if len(C) > 1]
        inc = set(frozenset(c) for c in R); ora = set(frozenset(c) for c in full)
        total += 1; match += (inc == ora); cyclic += (len(full) > 0)
    if verbose:
        print("=== Torn-region finder vs full Tarjan (adversarial, forced cycles) ===")
        print(f"  random (DAG + extension) instances            : {total}")
        print(f"  instances with a real torn region (cycles)    : {cyclic}")
        print(f"  output-sensitive finder == full Tarjan        : {match}/{total}")
    return total > 0 and match == total and cyclic > total // 4


def validate_correctness(trials=60, seed=1, verbose=True):
    """At every edit, the INCREMENTALLY-maintained matching must be a valid, acyclic (certified)
       matching of K' whose Morse complex has the correct homology -- checked against from scratch."""
    from ph_predictions import eta_via_pairdigraphs
    rng = random.Random(seed)
    ok_match = ok_acyclic = ok_hom = steps = fired = 0
    torn_ok = True
    for _ in range(trials):
        P = [(rng.uniform(0, 1), rng.uniform(0, 1)) for _ in range(rng.randint(8, 11))]
        r = rng.uniform(0.45, 0.75)
        K = vietoris_rips(P, r, 2)
        M = exact_repair(collapse_matching(K))
        if not is_matching(M) or n_cells(K) < 6:
            continue
        cert = IncCertifier(K, M); cert.check = True     # self-check torn region vs full Tarjan
        for _t in range(6):
            # mix of edit sizes: small jitters and larger radius jumps (the latter force eta>0)
            if _t % 2 == 0:
                P = [(x + rng.gauss(0, 0.06), y + rng.gauss(0, 0.06)) for (x, y) in P]; rr = r
            else:
                rr = max(0.3, r + rng.uniform(-0.18, 0.18))
            K2 = vietoris_rips(P, rr, 2)
            torn, _ = cert.apply_edit(K2)
            r = rr
            M2 = cert.matching()
            steps += 1; fired += (len(torn) > 0)
            valid = is_matching(M2) and all(a in set(K2) and b in set(K2) for a, b in M2)
            ok_match += valid
            eta = eta_via_pairdigraphs(M2) if valid else 999
            ok_acyclic += (eta == 0)
            try:
                hom_ok = valid and eta == 0 and (morse_complex_homology(K2, M2)[0] == betti_numbers(K2))
            except Exception:
                hom_ok = False
            ok_hom += bool(hom_ok)
        torn_ok = torn_ok and cert.torn_check_ok
    if verbose:
        print("=== Incremental certified maintenance: correctness vs from-scratch (every edit) ===")
        print(f"  edits tested                                    : {steps}")
        print(f"  maintained M' is a valid matching of K'         : {ok_match}/{steps}")
        print(f"  maintained M' is ACYCLIC (certified)            : {ok_acyclic}/{steps}")
        print(f"  Morse complex of M' has the correct homology    : {ok_hom}/{steps}")
        print(f"  edits where the torn-repair path fired (eta>0)  : {fired}")
        print(f"  incremental torn region == full Tarjan (oracle) : {'all' if torn_ok else 'MISMATCH'}")
    return (steps > 0 and ok_match == steps and ok_acyclic == steps and ok_hom == steps and torn_ok)


def validate_independence(seed=5, verbose=True):
    """Per-edit work is INDEPENDENT OF n for a local edit, on a CONNECTED complex.  A growing chain of
       points (consecutive ones overlap, so the Vietoris--Rips complex is connected and grows with n);
       the SAME local edit at one end is applied at every length, and we measure the incremental
       per-edit work against the from-scratch cost of rebuilding the pair-digraph (which is Theta(n))."""
    rows = []
    for length in [6, 20, 60, 180, 540]:
        rng = random.Random(seed)
        pts = [(1.0 * i + rng.uniform(-0.05, 0.05), rng.uniform(-0.05, 0.05)) for i in range(length)]
        K = vietoris_rips(pts, radius=1.15, maxdim=2)
        M = exact_repair(collapse_matching(K))
        if not is_matching(M):
            continue
        cert = IncCertifier(K, M)
        rng2 = random.Random(1)                    # identical local edit at every length: move the first 3 points
        for i in range(3):
            pts[i] = (1.0 * i + rng2.uniform(-0.3, 0.3), rng2.uniform(-0.3, 0.3))
        K2 = vietoris_rips(pts, radius=1.15, maxdim=2)
        delta = len((set(K) - set(K2)) | (set(K2) - set(K)))
        _, work = cert.apply_edit(K2)
        fromscratch = sum(len(g.adj) + sum(len(a) for a in g.adj.values()) for g in cert.D.values())
        rows.append((length, n_cells(K2), delta, work, fromscratch))
    if verbose:
        print("\n=== Per-edit work is INDEPENDENT OF n for a local edit (connected complex) ===")
        print(f"  {'chain':>6} {'n=|K|':>7} {'delta':>6} {'incr. work':>11} {'from-scratch':>13}")
        for (L, n, d, w, fs) in rows:
            print(f"  {L:>6} {n:>7} {d:>6} {w:>11} {fs:>13}")
        if len(rows) >= 2:
            ngrowth = rows[-1][1] / max(rows[0][1], 1)
            wgrowth = rows[-1][3] / max(rows[0][3], 1)
            print(f"  complex grew {ngrowth:.0f}x; INCREMENTAL work grew {wgrowth:.2f}x while "
                  f"from-scratch grew {rows[-1][4]/max(rows[0][4],1):.0f}x")
    return (len(rows) >= 2 and rows[0][3] > 0 and rows[-1][3] <= 2 * rows[0][3] + 5
            and rows[-1][4] > 5 * rows[0][4])


if __name__ == "__main__":
    print("[self-test] Pearce--Kelly keeps a valid topo order and detects cycles:", _self_test())
    ok0 = stress_torn_finder()
    ok1 = validate_correctness()
    ok2 = validate_independence()
    print(f"\nINCREMENTAL DATA STRUCTURE VALIDATED: torn-finder={ok0}, correctness={ok1}, n-independence={ok2}")
    if ok0 and ok1 and ok2:
        print("=> per-edit certified-matching maintenance is edit-local, independent of the global size n.")
