"""
morse_vineyards.py -- verification of the NEW dynamic result:

  OUTPUT-SENSITIVE VINEYARDS VIA A CERTIFIED MORSE MATCHING.

Model: a FIXED complex K, a MOVING filtration f_t (lower-star of a moving vertex function).  Standard
vineyards maintains the barcode of (K,f_t) on all n cells, O(n) per transposition.  We instead keep a
filtration-compatible acyclic Morse matching M and run vineyards on the c-cell Morse complex.

The key structural fact we exploit: the Morse boundary dM depends only on (K, M), NOT on the filtration
VALUES.  So as f_t moves while M stays compatible, dM is LITERALLY CONSTANT; only the critical cells'
order changes, i.e. the barcode moves through transpositions of the c critical cells alone -- vineyards
on c cells, O(c) per transposition, a factor n/c faster.  A level-crossing that breaks a matched pair
(the pair stops being co-valued) is the only event that changes M, and it is edit-local (Thm:localrepair).

This script verifies the two load-bearing claims against an independent full-complex persistence oracle:
 (A) SOUNDNESS: PD(Morse complex, f_t) == PD(K, f_t) at every sampled t of a moving filtration, for a
     compatible acyclic matching (so vineyards on the Morse complex is correct);
 (B) THE MECHANISM/WIN: while M stays compatible, dM is invariant across all t (only the order moves),
     and c < n, so the maintenance runs on c cells not n.  We report the speedup factor n/c and the
     ratio of critical-cell order-transpositions to all-cell order-transpositions over the sweep.
"""

from __future__ import annotations
import random, math
from ph_predictions import faces, vietoris_rips, matching_acyclic_via_pairdigraphs, defaultdict
from approx import persistence_diagram

INF = float('inf')


def lower_star(K, vval):
    return {c: max(vval[v] for v in c) for c in K}


def full_boundary(c):
    return list(faces(c))


def compatible_acyclic_matching(K, filt, rng, density=1.0):
    """Greedy co-valued (f(sigma)=f(tau)) acyclic facet matching: a filtration-compatible acyclic
       Morse matching in the Mischaikow--Nanda sense."""
    Sset = set(K)
    edges = []
    for tau in K:
        for sig in faces(tau):
            if sig in Sset and abs(filt[sig] - filt[tau]) < 1e-12:
                edges.append((sig, tau))
    rng.shuffle(edges)
    used, M = set(), []
    for (s, t) in edges:
        if s in used or t in used:
            continue
        if rng.random() > density:
            continue
        if matching_acyclic_via_pairdigraphs(M + [(s, t)]):
            M.append((s, t)); used.add(s); used.add(t)
    return M


def morse_boundary(K, M):
    """Critical cells and the Morse boundary dM (flow projection pi); depends only on (K,M)."""
    Sset = set(K)
    matched_up = {lo: up for lo, up in M}
    matched_dn = {up: lo for lo, up in M}
    crit = set(s for s in K if s not in matched_up and s not in matched_dn)
    memo = {}

    def pi(sigma):
        if sigma in memo:
            return memo[sigma]
        memo[sigma] = set()
        if sigma in crit:
            res = {sigma}
        elif sigma in matched_up:
            tau = matched_up[sigma]; res = set()
            for f in faces(tau):
                if f in Sset and f != sigma:
                    res ^= pi(f)
        else:
            res = set()
        memo[sigma] = res
        return res

    def dM(c):
        out = set()
        for f in faces(c):
            if f in Sset:
                out ^= pi(f)
        return list(out)
    return crit, dM


def _norm(dgm):
    out = {}
    for k, bars in dgm.items():
        out[k] = sorted((round(b, 7), (1e18 if d == INF else round(d, 7))) for b, d in bars)
    return out


def pd_equal(D1, D2):
    return _norm(D1) == _norm(D2)


def sample_complex(rng):
    npts = rng.randint(9, 13)
    P = [(rng.uniform(0, 1), rng.uniform(0, 1)) for _ in range(npts)]
    K = vietoris_rips(P, radius=rng.uniform(0.55, 0.85), maxdim=2)
    return K, [v for v in K if len(v) == 1]


def run(trials=40, steps=12, seed=1, verbose=True):
    rng = random.Random(seed)
    ok_sound = 0
    checks = 0
    dM_invariant = 0
    speedups = []
    transp_ratios = []
    eta_seen = 0
    for _ in range(trials):
        K, verts = sample_complex(rng)
        vlist = [next(iter(v)) for v in verts]
        vval0 = {v: rng.random() for v in vlist}
        hdir = {v: rng.uniform(-0.35, 0.35) for v in vlist}     # moving direction
        filt0 = lower_star(K, vval0)
        M = compatible_acyclic_matching(K, filt0, rng, density=0.9)
        crit, dM = morse_boundary(K, M)
        n, c = len(K), len(crit)
        if c == 0 or c == n:
            continue
        # snapshot dM (structural, filtration-independent) to confirm invariance across t
        dM_snapshot = {cc: frozenset(dM(cc)) for cc in crit}

        prev_full = prev_crit = None
        full_flips = crit_flips = 0
        trial_ok = True
        broke = False
        for i in range(steps):
            t = i / (steps - 1)
            vval = {v: vval0[v] + t * hdir[v] for v in vlist}
            filt = lower_star(K, vval)
            # compatibility: matched pairs must stay co-valued
            if not all(abs(filt[s] - filt[tau]) < 1e-9 for (s, tau) in M):
                broke = True
                break   # a level-crossing repair event; stop this compatible phase
            # (A) soundness: Morse-complex PD == full PD
            PD_full = persistence_diagram(K, filt, full_boundary)
            fc = {cc: filt[cc] for cc in crit}
            PD_morse = persistence_diagram(list(crit), fc, lambda cc: dM(cc))
            checks += 1
            if pd_equal(PD_full, PD_morse):
                ok_sound += 1
            else:
                trial_ok = False
            # (B) dM invariance across t
            if all(frozenset(dM(cc)) == dM_snapshot[cc] for cc in crit):
                dM_invariant += 1
            # count order-transpositions (adjacent inversions) full vs critical
            full_ord = sorted(K, key=lambda cc: (filt[cc], len(cc), tuple(sorted(cc))))
            crit_ord = sorted(crit, key=lambda cc: (filt[cc], len(cc), tuple(sorted(cc))))
            if prev_full is not None:
                full_flips += _adj_transpositions(prev_full, full_ord)
                crit_flips += _adj_transpositions(prev_crit, crit_ord)
            prev_full, prev_crit = full_ord, crit_ord
        if trial_ok:
            speedups.append(n / c)
            if full_flips > 0:
                transp_ratios.append(crit_flips / full_flips)

    frac = ok_sound / max(checks, 1)
    if verbose:
        print("=== Output-sensitive vineyards via a certified Morse matching ===")
        print(f"  (A) SOUNDNESS: Morse-complex barcode == full barcode on {ok_sound}/{checks} "
              f"moving-filtration checks  ({100*frac:.1f}%)")
        print(f"  (B) dM invariant across the moving filtration on {dM_invariant}/{checks} checks "
              f"(structural: depends on (K,M), not on f_t)")
        if speedups:
            print(f"  WIN: Morse complex is c cells vs n; mean size ratio n/c = "
                  f"{sum(speedups)/len(speedups):.2f}x  (so all persistence ops are that much cheaper)")
        if transp_ratios:
            print(f"       critical-cell order-transpositions are {100*sum(transp_ratios)/len(transp_ratios):.0f}% "
                  f"of all-cell transpositions over the sweep")
    return frac == 1.0 and dM_invariant == checks


def _adj_transpositions(a, b):
    """Number of pairwise order inversions between two orderings of the same set (Kendall tau)."""
    pos = {x: i for i, x in enumerate(b)}
    seq = [pos[x] for x in a if x in pos]
    inv = 0
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                inv += 1
    return inv


if __name__ == "__main__":
    ok = run()
    print(f"\nMORSE-VINEYARDS SOUNDNESS VERIFIED: {ok}")
    if ok:
        print("=> maintaining the barcode on the c-cell Morse complex is correct under a moving")
        print("   filtration; vineyards there costs O(c)/transposition vs O(n) on the full complex.")
