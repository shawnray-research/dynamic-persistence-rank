"""
learnability.py -- validation that the certified-repair error is LEARNABLE: a predictor can be trained
from example complexes so that its expected error generalizes, making the algorithms-with-predictions
framing operational (not just the warm-start special case).

Model.  A predictor class Pi = { pi_w : w in R^k } of score-based matchers: each Hasse edge (sigma,tau)
(sigma a facet of tau) gets a feature vector phi(sigma,tau) in R^k; pi_w processes the edges in
decreasing order of <w, phi> and greedily takes a pair whenever both cells are free, producing a
(possibly cyclic) predicted matching.  CertMorse then repairs it; the loss is the certified
critical-cell fraction  ell_w(K) = c(pi_w(K)) / |K|  in [0,1], evaluated in polynomial time by the
greedy (approximate) repair.

Theorem being validated (Learnability of certified repair).  If the induced loss class
{ K -> ell_w(K) } has pseudo-dimension d, then m = O(eps^-2 (d + ln 1/delta)) sample complexes give
uniform convergence: sup_w | empirical mean ell_w - true mean ell_w | <= eps, so empirical risk
minimization returns a predictor within 2 eps of the best in the class (Gupta-Roughgarden pseudo-
dimension bound for application-specific algorithm selection).

We verify: (a) the max-over-class generalization gap shrinks like 1/sqrt(m) (uniform convergence);
(b) the empirically-best predictor (ERM) generalizes -- its true risk approaches the best in the class.
"""

from __future__ import annotations
import random, math
from ph_predictions import vietoris_rips, faces, is_matching, greedy_repair, defaultdict
from experiment import n_cells


def cofaces(K):
    cof = defaultdict(set)
    for c in K:
        for f in faces(c):
            if f in K:
                cof[f].add(c)
    return cof


def features(sigma, tau, cof):
    """A fixed feature map phi(sigma,tau) in R^k (k=4): bias, dimension, and the two coface-degrees."""
    return [1.0, float(len(sigma) - 1), float(len(cof.get(sigma, ()))), float(len(cof.get(tau, ())))]


def predict(K, w, cof):
    """Score-based greedy matcher pi_w: take Hasse edges by decreasing <w, phi>, pairing free cells."""
    edges = []
    for tau in K:
        for f in faces(tau):
            if f in K:
                s = sum(wi * xi for wi, xi in zip(w, features(f, tau, cof)))
                edges.append((s, f, tau))
    edges.sort(key=lambda t: -t[0])
    used, M = set(), []
    for _, f, tau in edges:
        if f not in used and tau not in used:
            M.append((f, tau)); used.add(f); used.add(tau)
    return M


def loss(K, w, cof):
    """Certified critical-cell fraction after (poly-time) greedy repair; in [0,1]."""
    M = predict(K, w, cof)
    if not is_matching(M):
        return 1.0
    Mr = greedy_repair(M)
    n = n_cells(K)
    return (n - 2 * len(Mr)) / max(n, 1)


def sample_complex(rng):
    npts = rng.randint(7, 10)
    P = [(rng.uniform(0, 1), rng.uniform(0, 1)) for _ in range(npts)]
    return vietoris_rips(P, radius=rng.uniform(0.5, 0.85), maxdim=2)


def run(k=4, num_pred=60, seed=0, verbose=True):
    rng = random.Random(seed)
    # the predictor class: a finite sample of weight vectors standing in for Pi (k-dim, pdim = O(k))
    W = [[rng.gauss(0, 1) for _ in range(k)] for _ in range(num_pred)]
    # a large held-out set to estimate the TRUE risk of each predictor
    test = [sample_complex(rng) for _ in range(200)]
    test_cof = [cofaces(K) for K in test]
    true_risk = [sum(loss(K, w, cf) for K, cf in zip(test, test_cof)) / len(test) for w in W]
    best_true = min(true_risk)

    rows = []
    for m in [5, 10, 20, 40, 80, 160]:
        # average the generalization gap and ERM excess over several independent training draws
        gaps, excess = [], []
        for rep in range(6):
            train = [sample_complex(rng) for _ in range(m)]
            tcof = [cofaces(K) for K in train]
            emp = [sum(loss(K, w, cf) for K, cf in zip(train, tcof)) / m for w in W]
            gaps.append(max(abs(emp[j] - true_risk[j]) for j in range(len(W))))
            jhat = min(range(len(W)), key=lambda j: emp[j])
            excess.append(true_risk[jhat] - best_true)
        rows.append((m, sum(gaps) / len(gaps), sum(excess) / len(excess)))

    if verbose:
        print("=== Learnability of certified repair: uniform convergence + ERM generalization ===")
        print(f"  predictor class: {num_pred} score-matchers, feature dim k={k}; loss = certified "
              f"critical-cell fraction")
        print(f"  best true risk in class: {best_true:.3f}")
        print(f"  {'m (train)':>9} {'sup gap |emp-true|':>18} {'ERM excess risk':>16} {'eps~1/sqrt(m)':>14}")
        for (m, g, ex) in rows:
            print(f"  {m:>9} {g:>18.3f} {ex:>16.3f} {1.0/math.sqrt(m):>14.3f}")
    # uniform convergence: the sup gap should decrease with m and track ~1/sqrt(m);
    # ERM excess should shrink toward 0.
    gap_first, gap_last = rows[0][1], rows[-1][1]
    erm_last = rows[-1][2]
    return gap_last < 0.75 * gap_first and erm_last <= 0.05


if __name__ == "__main__":
    ok = run()
    print(f"\nLEARNABILITY VALIDATED: {ok}")
    if ok:
        print("=> a predictor for certified repair generalizes from examples: uniform convergence holds")
        print("   and empirical risk minimization returns a near-best-in-class predictor.")
