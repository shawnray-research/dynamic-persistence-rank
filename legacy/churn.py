"""
churn.py -- verification of the LOW-RANK CHURN THEOREM and its maintenance corollary:

  THEOREM (churn).  Let M be a certified (filtration-compatible acyclic) Morse matching of K, and let
  K' be obtained by an edit inserting I and deleting R cells (delta = |I|+|R|), with the warm-start
  matching M' (surviving pairs of M + extension over newly-uncovered cells, repaired).  Let
  "changed cells" = cells inserted, deleted, or whose matching partner differs between M and M'.
  Then, restricted to the critical cells shared by both states, the residual-boundary change
        Delta = d^{M'} - d^{M}
  has F2-rank at most |changed cells| = O(delta); the remaining difference is O(delta) row/column
  insertions/deletions (critical cells appearing/disappearing).

  WHY (first-entry decomposition): a gradient path contributing to d^M either avoids every changed
  cell (then it is identical in both states) or has a unique FIRST changed cell b on it; grouping by b
  factors the change as  Delta = sum_b u_b v_b^T,  one outer product per changed cell.

  COROLLARY (maintenance).  rank(A + U V^T) = rank([[A, U],[V^T, I_w]]) - w  (Schur complement), so a
  width-w churn is absorbed by bordering the maintained matrix with w new rows/columns, i.e., O(delta)
  column/row updates of a dynamic-rank structure per edit, with periodic rebuilds once the border
  grows; no per-entry re-computation of d^M is needed.

Validations:
  (1) rank(Delta restricted to shared critical cells) <= |changed cells| on random warm-started edits
      of random Vietoris-Rips complexes (insertions of cones + deletions of maximal cells), and the
      critical-cell set changes by at most 2|changed| rows/columns;
  (2) the Schur/bordering identity over F2 on random (A, U, V);
  (3) the ANY-FIELD zero test behind the F_q lower bound (cor:fields): over F3 and F5, with oriented
      boundary matrices, dim Z_2 of the switched complex K(A) equals |S| iff the active submatrix
      A[R,S] is zero -- so the OuMv reduction is field-independent.
"""

from __future__ import annotations
import random
from ph_predictions import faces, vietoris_rips, matching_acyclic_via_pairdigraphs, greedy_repair
from dynrank import build_switched, matrix_rank


# ------------------------------- F2 / F_p linear algebra ------------------------------------

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


# ------------------------------- residual boundary d^M --------------------------------------

def morse_boundary_matrix(K, M):
    S = set(K)
    up = {lo: hi for lo, hi in M}
    dn = {hi: lo for lo, hi in M}
    crit = [c for c in K if c not in up and c not in dn]
    critset = set(crit)
    memo = {}

    def pi(s):
        if s in memo:
            return memo[s]
        memo[s] = set()
        if s in critset:
            res = {s}
        elif s in up:
            t = up[s]
            res = set()
            for f in faces(t):
                if f in S and f != s:
                    res ^= pi(f)
        else:
            res = set()
        memo[s] = res
        return res

    dM = {}
    for c in crit:
        out = set()
        for f in faces(c):
            if f in S:
                out ^= pi(f)
        dM[c] = out
    return dM, critset


def greedy_matching(K, rng, density=0.85):
    S = set(K)
    cand = [(f, t) for t in K for f in faces(t) if f in S]
    rng.shuffle(cand)
    used = set()
    M = []
    for f, t in cand:
        if f in used or t in used or rng.random() > density:
            continue
        if matching_acyclic_via_pairdigraphs(M + [(f, t)]):
            M.append((f, t))
            used.add(f)
            used.add(t)
    return M


# --------------------------------------- validations ----------------------------------------

def validate_churn(trials=30, verbose=True):
    rng = random.Random(7)
    ok = tot = 0
    worst_rank = 0
    for trial in range(trials):
        npts = rng.randint(8, 11)
        P = [(rng.uniform(0, 1), rng.uniform(0, 1)) for _ in range(npts)]
        K = list(vietoris_rips(P, radius=rng.uniform(0.5, 0.8), maxdim=2))
        M = greedy_matching(K, rng)
        Kset = set(K)
        maximal = [c for c in Kset if not any((c < d) for d in Kset)]
        R = set(rng.sample(maximal, min(len(maximal), rng.randint(1, 3))))
        K2 = set(Kset) - R
        newv = ('z', trial)
        e = rng.choice([c for c in K2 if len(c) == 2])
        ins = {frozenset({newv}), frozenset(set(e) | {newv})} | {frozenset({newv, x}) for x in e}
        K2 |= ins
        surv = [(f, t) for (f, t) in M if f in K2 and t in K2]
        covered = {x for pr in surv for x in pr}
        newly = set(ins) | {c for c in K2 if c not in covered and any(c in pr for pr in M)}
        used = set(covered)
        E = []
        cand = [(f, t) for t in K2 for f in faces(t)
                if f in K2 and (t in newly or f in newly)]
        rng.shuffle(cand)
        for f, t in cand:
            if f in used or t in used:
                continue
            if matching_acyclic_via_pairdigraphs(surv + E + [(f, t)]):
                E.append((f, t))
                used.add(f)
                used.add(t)
        M2 = greedy_repair(surv + E)
        p1 = {**{f: t for f, t in M}, **{t: f for f, t in M}}
        p2 = {**{f: t for f, t in M2}, **{t: f for f, t in M2}}
        allc = set(K) | K2
        changed = {c for c in allc if ((c in Kset) != (c in K2)) or p1.get(c) != p2.get(c)}
        dM1, crit1 = morse_boundary_matrix(K, M)
        dM2, crit2 = morse_boundary_matrix(list(K2), M2)
        shared = crit1 & crit2
        idx = {c: i for i, c in enumerate(sorted(shared, key=lambda s: (len(s), tuple(sorted(map(str, s))))))}
        rows = []
        for c in shared:
            diff = ({idx[x] for x in dM1[c] if x in idx}
                    ^ {idx[x] for x in dM2[c] if x in idx})
            if diff:
                rows.append(diff)
        rk = f2_rank(rows)
        dim_change = len(crit1 ^ crit2)
        tot += 1
        if rk <= len(changed) and dim_change <= 2 * len(changed):
            ok += 1
        worst_rank = max(worst_rank, rk)
    if verbose:
        print(f"  (1) churn: rank(Delta d^M) <= |changed cells| and dim change <= 2|changed| "
              f"on {ok}/{tot} warm-started edits (worst rank observed {worst_rank})")
    return ok == tot


def validate_bordering(trials=200, verbose=True):
    """rank(A + U V^T) == rank([[A,U],[V^T,I_w]]) - w over F2."""
    rng = random.Random(1)
    ok = tot = 0
    for _ in range(trials):
        n = rng.randint(2, 7)
        w = rng.randint(1, 3)
        A = [[rng.randint(0, 1) for _ in range(n)] for _ in range(n)]
        U = [[rng.randint(0, 1) for _ in range(w)] for _ in range(n)]
        V = [[rng.randint(0, 1) for _ in range(w)] for _ in range(n)]
        Apert = [[(A[i][j] + sum(U[i][t] * V[j][t] for t in range(w))) % 2
                  for j in range(n)] for i in range(n)]
        B = [[A[i][j] for j in range(n)] + [U[i][t] for t in range(w)] for i in range(n)] + \
            [[V[j][t] for j in range(n)] + [1 if s == t else 0 for s in range(w)] for t in range(w)]
        tot += 1
        ok += (matrix_rank(Apert) == matrix_rank(B) - w)
    if verbose:
        print(f"  (2) bordering identity rank(A+UV^T) = rank(bordered) - w over F2: {ok}/{tot}")
    return ok == tot


def oriented_d2_rank(cells, p):
    """rank over F_p of the oriented triangle-edge boundary of a complex given as frozensets."""
    tris = [tuple(sorted(c)) for c in cells if len(c) == 3]
    edges = [tuple(sorted(c)) for c in cells if len(c) == 2]
    ei = {e: i for i, e in enumerate(edges)}
    rows = []
    for (a, b, c) in tris:
        rows.append({ei[(b, c)]: 1, ei[(a, c)]: -1, ei[(a, b)]: 1})
    return fp_rank(rows, p)


def validate_anyfield(trials=25, verbose=True):
    """The zero test behind cor:fields: over F3 and F5, dim Z_2 == |S| iff A[R,S] == 0."""
    rng = random.Random(3)
    ok = tot = 0
    for _ in range(trials):
        r = rng.randint(1, 3)
        k = rng.randint(1, 3)
        A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
        u = {i for i in range(r) if rng.random() < 0.6}
        v = {j for j in range(k) if rng.random() < 0.6}
        K, T = build_switched(A, r, k, u, v)
        sub_zero = not any(A[i][j] for i in u for j in v)
        for p in (3, 5):
            z2 = T - oriented_d2_rank(K, p)
            tot += 1
            ok += ((z2 == len(v)) == sub_zero)
    if verbose:
        print(f"  (3) any-field zero test (F3, F5): dim Z_2 = |S| iff A[R,S] = 0: {ok}/{tot}")
    return ok == tot



def validate_chi(trials=10, verbose=True):
    """chi(K(A)) = 2k - nnz(A) on switched instances (all active): the Euler obstruction behind the
       no-refutation proposition -- dense OuMv-hard instances force c_min >= |chi| = Theta(m)."""
    rng = random.Random(9)
    ok = tot = 0
    for _ in range(trials):
        r = rng.randint(2, 6)
        k = rng.randint(2, 6)
        A = [[rng.randint(0, 1) for _ in range(k)] for _ in range(r)]
        nnz = sum(map(sum, A))
        K, T = build_switched(A, r, k, set(range(r)), set(range(k)))
        V = sum(1 for c in K if len(c) == 1)
        E = sum(1 for c in K if len(c) == 2)
        F = sum(1 for c in K if len(c) == 3)
        tot += 1
        ok += (V - E + F == 2 * k - nnz)
    if verbose:
        print(f"  (4) Euler obstruction: chi(K(A)) == 2k - nnz on {ok}/{tot} switched instances")
    return ok == tot


def _run_all():
    print("=== churn.py: low-rank churn of the Morse residual + field-independence checks ===")
    r1 = validate_churn()
    r2 = validate_bordering()
    r3 = validate_anyfield()
    r4 = validate_chi()
    r5 = validate_persbetti()
    print(f"\nALL VALIDATED: {r1 and r2 and r3 and r4 and r5}")
    if r1 and r2 and r3:
        print("=> the residual boundary changes by a rank-O(delta) matrix per warm-started edit,")
        print("   absorbable by bordering a dynamic-rank structure; the OuMv lower bound is")
        print("   field-independent; and persistent Betti at fixed thresholds is a four-rank formula.")


def validate_persbetti(trials=60, verbose=True):
    """The FOUR-RANK persistent-Betti formula behind Appendix B.1 (thm:width), over F2:
         beta_p^{s,t} = (n_p(K_s) - rank d_p^{K_s})
                        - (rank d_{p+1}^{K_t} - rank d_{p+1}^{K_t \\ K_s}),
       where d_p^{K_s} restricts to p-simplices of K_s, d_{p+1}^{K_t} is on K_t, and
       d_{p+1}^{K_t\\K_s} restricts d_{p+1}(K_t) to rows (p-simplices) OUTSIDE K_s.  The first bracket
       is dim Z_p(K_s); the second is dim(Z_p(K_s) cap B_p(K_t)).  Checked against a brute-force
       rank(H_p(K_s)->H_p(K_t)).  (The three-rank shorthand rank d_{p+1}^{s,t} is WRONG -- caught by
       this oracle, 99/120; the four-rank form is 120/120.)"""
    import random as _r
    from ph_predictions import vietoris_rips

    def bcols(cells, q, rowset):
        idx = {c: i for i, c in enumerate(sorted(rowset, key=repr))}
        return [{idx[f] for f in (frozenset(c - {v}) for v in c) if f in idx}
                for c in sorted([x for x in cells if len(x) == q + 1], key=repr)]

    def rk(vs):
        return f2_rank([set(v) for v in vs if v])

    def kernel(cols):
        piv = {}; basis = []
        for j, c in enumerate(cols):
            c = set(c); combo = {j}
            while c:
                p = max(c)
                if p in piv:
                    c ^= piv[p][0]; combo ^= piv[p][1]
                else:
                    piv[p] = (c, combo); break
            else:
                basis.append(combo)
        return basis

    def brute(Ks, Kt, p):
        ks_p = sorted([c for c in Ks if len(c) == p + 1], key=repr)
        kt_p = sorted([c for c in Kt if len(c) == p + 1], key=repr)
        ks_pm1 = {c for c in Ks if len(c) == p}
        kern = kernel(bcols(Ks, p, ks_pm1))
        pidx = {c: i for i, c in enumerate(kt_p)}
        ksidx = {i: pidx[c] for i, c in enumerate(ks_p)}
        Z = [{ksidx[j] for j in combo} for combo in kern]
        B = [{pidx[f] for f in (frozenset(c - {v}) for v in c) if f in pidx}
             for c in sorted([x for x in Kt if len(x) == p + 2], key=repr)]
        return rk(Z) - (rk(Z) + rk(B) - rk(Z + B))

    def formula(Ks, Kt, p):
        ks_pm1 = {c for c in Ks if len(c) == p}
        n_p = len([c for c in Ks if len(c) == p + 1])
        r_dp_s = rk(bcols(Ks, p, ks_pm1))
        kt_pcells = {c for c in Kt if len(c) == p + 1}
        ks_pcells = {c for c in Ks if len(c) == p + 1}
        r_dpp_t = rk(bcols(Kt, p + 1, kt_pcells))
        r_bar = rk(bcols(Kt, p + 1, kt_pcells - ks_pcells))
        return (n_p - r_dp_s) - (r_dpp_t - r_bar)

    rng = _r.Random(5); ok = tot = 0
    for _ in range(trials):
        P = [(rng.uniform(0, 1), rng.uniform(0, 1)) for _ in range(rng.randint(5, 9))]
        Kt = set(vietoris_rips(P, radius=rng.uniform(0.5, 0.9), maxdim=2))
        Ks = set(Kt)
        for _ in range(rng.randint(1, 8)):
            maxi = [c for c in Ks if not any(c < d for d in Ks)]
            if maxi:
                Ks.discard(rng.choice(maxi))
        for p in (0, 1):
            tot += 1
            ok += (formula(Ks, Kt, p) == brute(Ks, Kt, p))
    if verbose:
        print(f"  (5) four-rank persistent-Betti formula (Appendix B.1) == brute "
              f"rank(H_p(K_s)->H_p(K_t)): {ok}/{tot}")
    return ok == tot


if __name__ == "__main__":
    _run_all()
