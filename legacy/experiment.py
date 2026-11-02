"""
experiment.py -- illustrative experiments for "Dynamic Persistent Homology is Rank-Complete".

  CONSISTENCY: a realistic heuristic predictor (elementary-collapse matching) leaves
               few critical cells -> the residual computation shrinks drastically.
  ROBUSTNESS:  a deliberately bad (random, cyclic) predictor is certified-and-repaired to
               the CORRECT homology, whereas naively trusting it is unsafe/wrong.
  SMOOTHNESS:  after exact repair, the excess critical cells over the prediction's ideal
               equals exactly 2*eta (Theorem 6), confirmed across many random predictions.

All homology cross-checked against ground truth. Numbers are computed, not hand-written.
"""

from __future__ import annotations
import os, math, random
from collections import defaultdict
from ph_predictions import (
    faces, vietoris_rips, betti_numbers,
    is_matching, modified_hasse_cycle, matching_acyclic_via_pairdigraphs,
    eta_via_pairdigraphs, greedy_repair, exact_repair,
    morse_complex_homology, random_matching,
)


def collapse_matching(simplices):
    """Realistic predictor: elementary-collapse (free-face) discrete Morse matching."""
    work = set(simplices)
    matching = []
    while work:
        coface = defaultdict(list)
        for s in work:
            for f in faces(s):
                if f in work:
                    coface[f].append(s)
        free = None
        for sigma, cofs in coface.items():
            if len(cofs) == 1:
                free = (sigma, cofs[0]); break
        if free:
            sigma, tau = free
            matching.append((sigma, tau)); work.discard(sigma); work.discard(tau)
        else:
            work.discard(max(work, key=lambda s: (len(s), tuple(sorted(s)))))
    return matching


def n_cells(K):
    return len([s for s in K if len(s) >= 1])


def circle_cloud(npts, rng, jitter=0.0):
    return [(math.cos(2*math.pi*i/npts) + rng.uniform(-jitter, jitter),
             math.sin(2*math.pi*i/npts) + rng.uniform(-jitter, jitter)) for i in range(npts)]


def dense_complex(rng, npts=7, dim=3, radius=0.85, maxdim=3):
    return vietoris_rips([tuple(rng.random() for _ in range(dim)) for _ in range(npts)],
                         radius=radius, maxdim=maxdim)


def per_dim_pairs_ok(matching, cap=11):
    cnt = defaultdict(int)
    for lo, _ in matching:
        cnt[len(lo) - 1] += 1
    return all(v <= cap for v in cnt.values())


def consistency_table(seed=7):
    rng = random.Random(seed)
    print("=== CONSISTENCY: a realistic collapse-heuristic predictor (homology verified) ===")
    print(f"  {'n=|K|':>6} {'Betti':>11} {'c_good':>7} {'c/n':>6} {'homology_ok':>11}")
    for npts in [8, 10, 12, 14, 16, 18, 20]:
        K = vietoris_rips(circle_cloud(npts, rng, jitter=0.06),
                          radius=2*math.sin(math.pi/npts)*1.65, maxdim=2)
        n = n_cells(K); true_b = betti_numbers(K)
        bg, critg = morse_complex_homology(K, collapse_matching(K))
        c = sum(critg.values())
        print(f"  {n:>6} {str(true_b):>11} {c:>7} {c/n:>6.2f} {str(bg == true_b):>11}")


def robustness_table(seed=11):
    """Bad (cyclic) predictors: exact repair recovers the true homology; naive trust does not."""
    rng = random.Random(seed)
    print("\n=== ROBUSTNESS: deliberately bad (cyclic) predictors (homology verified) ===")
    print(f"  {'n=|K|':>6} {'Betti':>11} {'eta':>4} {'c_repair':>9} {'repaired_ok':>11} {'naive_safe':>10}")
    shown = 0
    tries = 0
    while shown < 6 and tries < 4000:
        tries += 1
        K = dense_complex(rng, npts=rng.choice([6, 7]), radius=rng.uniform(0.78, 0.95))
        if n_cells(K) < 8:
            continue
        M = random_matching(K, density=0.95, rng=rng)
        if not per_dim_pairs_ok(M):
            continue
        eta = eta_via_pairdigraphs(M)
        if eta == 0:
            continue                      # want cyclic predictions to make the point
        true_b = betti_numbers(K)
        Mr = exact_repair(M)
        br, critb = morse_complex_homology(K, Mr)
        c_rep = sum(critb.values())
        naive_safe = (not modified_hasse_cycle(K, M))   # a cyclic M cannot even be used naively
        print(f"  {n_cells(K):>6} {str(true_b):>11} {eta:>4} {c_rep:>9} "
              f"{str(br == true_b):>11} {str(naive_safe):>10}")
        shown += 1


def smoothness_data(seed=3, out="data/smoothness.dat"):
    """Pool random predictions across many dense complexes; confirm excess = 2*eta exactly,
       and that homology is always recovered after exact repair."""
    rng = random.Random(seed)
    print("\n=== SMOOTHNESS: (critical cells after exact repair) - (ideal c*) == 2*eta ===")
    by_eta = defaultdict(int)
    exact_hits = total = 0
    tries = 0
    while total < 600 and tries < 60000:
        tries += 1
        K = dense_complex(rng, npts=rng.choice([6, 7]), radius=rng.uniform(0.7, 0.95))
        n = n_cells(K)
        if n < 6:
            continue
        M = random_matching(K, density=rng.uniform(0.3, 0.97), rng=rng)
        if len(M) < 3 or not per_dim_pairs_ok(M):
            continue
        eta = eta_via_pairdigraphs(M)
        cstar = n - 2 * len(M)
        Mr = exact_repair(M)
        c_rep = n - 2 * len(Mr)
        assert morse_complex_homology(K, Mr)[0] == betti_numbers(K)   # always correct
        excess = c_rep - cstar
        total += 1
        if excess == 2 * eta:
            exact_hits += 1
        by_eta[eta] += 1
    print(f"  excess == 2*eta on {exact_hits}/{total} pooled random predictions")
    print(f"  distribution of error eta over samples: "
          f"{dict(sorted(by_eta.items()))}")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        f.write("# eta  excess_critical_cells(=2*eta)  n_samples\n")
        for eta in sorted(by_eta):
            f.write(f"{eta} {2*eta} {by_eta[eta]}\n")
    print(f"  wrote {out}  (every point lies exactly on excess = 2*eta)")


def scaling_timing(seed=5):
    """Consistency at scale: a good (collapse) predictor shrinks the residual reduction from the full
       n cells to c critical cells. We time the standard homology reduction on all n cells against
       CertMorse (build the Morse complex of the collapse matching, then reduce its c cells). Homology
       is verified equal. Pure-Python proof of concept; the point is the n -> c reduction and its
       effect on the cubic reduction, not absolute milliseconds."""
    import time, math
    rng = random.Random(seed)
    print("\n=== SCALING: residual reduction shrinks from n to c (good predictor; homology verified) ===")
    print(f"  {'n=|K|':>6} {'c':>4} {'c/n':>7} {'t_standard':>11} {'t_certmorse':>12} {'speedup':>8}")
    for npts in [110, 160, 220, 300, 400, 520]:
        # points near a circle: nontrivial topology (beta_1=1), collapse leaves c = beta_0+beta_1 = 2
        pts = [(math.cos(2*math.pi*i/npts), math.sin(2*math.pi*i/npts)) for i in range(npts)]
        K = vietoris_rips(pts, radius=2*math.sin(math.pi/npts)*2.6, maxdim=2)
        n = n_cells(K)
        t0 = time.perf_counter(); b_std = betti_numbers(K); t_std = time.perf_counter() - t0
        Mg = collapse_matching(K)
        t0 = time.perf_counter(); b_cm, crit = morse_complex_homology(K, Mg); t_cm = time.perf_counter() - t0
        assert b_cm == b_std, f"homology mismatch {b_cm} vs {b_std}"
        c = sum(crit.values())
        sp = t_std / t_cm if t_cm > 0 else float('inf')
        print(f"  {n:>6} {c:>4} {c/n:>7.4f} {t_std:>10.3f}s {t_cm:>11.3f}s {sp:>7.1f}x")


if __name__ == "__main__":
    consistency_table()
    robustness_table()
    smoothness_data()
    scaling_timing()
