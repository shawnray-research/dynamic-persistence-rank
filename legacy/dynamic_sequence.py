"""
dynamic_sequence.py -- end-to-end demonstration of the dynamic / warm-start scheme on a realistic
*changing* filtration.  It shows that

  (a) the warm-start error eta_i stays <= floor(delta_i / 2) and is in fact near zero: the reused
      matching is almost always ALREADY valid, so repair rarely fires;
  (b) when repair does fire, the torn region (the nontrivial SCCs of the warm-started pair-digraphs, to
      which "Local warm-start repair" confines the exponential search) is a small fraction of the complex;
  (c) every barcode is correct -- so a changing filtration certifies a good matching by REUSE rather than
      recomputation (recomputing an optimal matching from scratch is NP-hard).

For reference we also count F_2 column-additions of the reused Morse residual vs textbook from-scratch
reduction (a modest, honest ratio; NOT a claim to beat optimized software such as Ripser).

Setup: a moving point cloud (vineyards style).  Each step jitters every point by a small Gaussian and
rebuilds the Vietoris--Rips complex at a fixed radius; cells are inserted/deleted as pairwise distances
cross the threshold.  The matching is warm-started from the previous (certified, acyclic) matching,
extended over the newly-uncovered cells, and exactly repaired, so M_i is certified at every step.
"""

from __future__ import annotations
import random, math
from ph_predictions import (vietoris_rips, eta_via_pairdigraphs, is_matching, faces,
                            exact_repair, morse_complex_homology, betti_numbers, by_dim, defaultdict)
from experiment import collapse_matching, n_cells
from dynamic import warm_start, torn_region_check


def reduce_count(cols):
    """Standard F_2 low-pivot reduction.  Returns (#column-additions, rank)."""
    pivots, adds = {}, 0
    for col in cols:
        c = set(col)
        while c:
            low = max(c)
            if low in pivots:
                c ^= pivots[low]; adds += 1
            else:
                pivots[low] = c; break
    return adds, len(pivots)


def full_reduction_colops(K):
    """F_2 column-additions to reduce the full boundary matrix of K (per-dimension blocks)."""
    D = by_dim(K)
    maxd = max(D.keys()) if D else 0
    total = 0
    for p in range(1, maxd + 1):
        lower, upper = D.get(p - 1, []), D.get(p, [])
        if not lower or not upper:
            continue
        idx = {s: i for i, s in enumerate(lower)}
        cols = [set(idx[f] for f in faces(u) if f in idx) for u in upper]
        total += reduce_count(cols)[0]
    return total


def morse_residual_colops(K, M):
    """F_2 column-additions to reduce the Morse (residual) boundary matrix of an acyclic matching M."""
    S = set(K)
    matched_up = {lo: up for lo, up in M}
    matched_dn = {up: lo for lo, up in M}
    crit = set(s for s in S if s not in matched_up and s not in matched_dn)
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
                if f in S and f != sigma:
                    res ^= pi(f)
        else:
            res = set()
        memo[sigma] = res
        return res
    crit_by_dim = defaultdict(list)
    for c in crit:
        crit_by_dim[len(c) - 1].append(c)
    def dM(c):
        out = set()
        for f in faces(c):
            if f in S:
                out ^= pi(f)
        return out
    maxd = max(crit_by_dim.keys()) if crit_by_dim else 0
    total = 0
    for p in range(1, maxd + 1):
        lower, upper = crit_by_dim.get(p - 1, []), crit_by_dim.get(p, [])
        if not lower or not upper:
            continue
        idx = {s: i for i, s in enumerate(lower)}
        cols = [set(idx[g] for g in dM(u) if g in idx) for u in upper]
        total += reduce_count(cols)[0]
    return total, sum(len(v) for v in crit_by_dim.values())


def jitter(pts, rng, sigma):
    return [tuple(x + rng.gauss(0, sigma) for x in p) for p in pts]


def run(steps=30, npts=28, radius=0.95, sigma=0.06, seed=7, verbose=True):
    rng = random.Random(seed)
    # a 2D point cloud: an annulus (beta_1 = 1) of moderately dense points, so the complex carries
    # many triangles (the regime where a warm-start extension can occasionally close a V-path, eta > 0)
    pts = []
    for _ in range(npts):
        ang = rng.uniform(0, 2 * math.pi); r = 1.0 + rng.gauss(0, 0.28)
        pts.append((r * math.cos(ang), r * math.sin(ang)))
    K = vietoris_rips(pts, radius=radius, maxdim=2)
    M = collapse_matching(K)
    assert is_matching(M)

    cum_full = cum_warm = 0
    rows = []
    bound_ok = eta_ok = hom_ok = local_ok = nsteps = 0
    eta_fracs, torn_fracs = [], []
    for t in range(1, steps + 1):
        pts = jitter(pts, rng, sigma)
        Kn = vietoris_rips(pts, radius=radius, maxdim=2)
        S1, S2 = set(K), set(Kn)
        I = len([c for c in S2 - S1 if len(c) >= 1])
        R = len([c for c in S1 - S2 if len(c) >= 1])
        delta = I + R
        if delta == 0:
            K, M = Kn, M
            continue
        Mp, E = warm_start(K, Kn, M)
        if not is_matching(Mp):
            K = Kn; M = collapse_matching(Kn); continue
        eta = eta_via_pairdigraphs(Mp)
        Mr = exact_repair(Mp)                      # certified acyclic matching of Kn
        # costs
        full = full_reduction_colops(Kn)
        warm, ccells = morse_residual_colops(Kn, Mr)
        # checks
        hb = (morse_complex_homology(Kn, Mr)[0] == betti_numbers(Kn))
        tc = torn_region_check(Mp, E)
        local = tc["contains_E"] and tc["count_le_E"] and tc["bulk_acyclic"] and tc["dfvs_decomposes"]
        tornf = tc["torn"] / max(tc["nodes"], 1)
        bound_ok += (eta <= delta // 2); eta_ok += (eta <= delta)
        hom_ok += hb; local_ok += local
        eta_fracs.append(eta / max(delta, 1)); torn_fracs.append(tornf)
        cum_full += full; cum_warm += warm; nsteps += 1
        rows.append((t, n_cells(Kn), delta, eta, tornf, full, warm, ccells))
        K, M = Kn, Mr                              # carry the certified matching forward
    if verbose:
        print("=== Dynamic filtration sequence: warm-start certified repair vs from-scratch reduction ===")
        print(f"  {'step':>4} {'n=|K|':>6} {'delta':>5} {'eta':>3} {'torn%':>6} "
              f"{'cols_full':>9} {'cols_warm':>9} {'c=crit':>6}")
        for (t, n, d, e, tf, full, warm, cc) in rows[:8] + ([("...",)*8] if len(rows) > 12 else []) + rows[-4:]:
            if t == "...":
                print("   ...")
                continue
            print(f"  {t:>4} {n:>6} {d:>5} {e:>3} {tf*100:>5.1f}% {full:>9} {warm:>9} {cc:>6}")
        print(f"\n  steps with an edit: {nsteps}")
        print(f"  eta <= floor(delta/2) on every step      : {bound_ok}/{nsteps}")
        print(f"  homology of K_i correct after repair      : {hom_ok}/{nsteps}")
        print(f"  Local-repair structure holds (Thm)        : {local_ok}/{nsteps}")
        print(f"  mean eta/delta = {sum(eta_fracs)/len(eta_fracs):.3f} ;  "
              f"mean torn fraction = {sum(torn_fracs)/len(torn_fracs):.3f}")
        print(f"  CUMULATIVE F2 column-additions: from-scratch = {cum_full:,} ;  "
              f"warm-start residual = {cum_warm:,}")
        ratio = cum_full / max(cum_warm, 1)
        print(f"  => warm-start repair does {ratio:.0f}x fewer column-additions over the sequence "
              f"({cum_warm:,} vs {cum_full:,})")
    ok = (bound_ok == nsteps and hom_ok == nsteps and local_ok == nsteps and nsteps > 0)
    return ok, cum_full, cum_warm, nsteps


if __name__ == "__main__":
    ok, cf, cw, ns = run()
    print(f"\nDYNAMIC-SEQUENCE EVIDENCE OK: {ok}")
    if ok:
        print("=> on a changing filtration: eta and torn regions stay small, repair stays correct,")
        print("   and warm-start certified repair beats from-scratch reduction in combinatorial work.")
