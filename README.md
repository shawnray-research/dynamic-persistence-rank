# Verification suite — *Dynamic Persistent Homology is Rank-Complete*

Independent computational validation for the paper **"Dynamic Persistent Homology is Rank-Complete:
The Complexity of Maintaining Betti Numbers."**

The code is **not part of any proof**. Its sole role is confidence: every combinatorial identity the
proofs rest on is checked against an independent brute-force oracle (direct boundary-matrix reduction,
exhaustive small instances, and randomized larger ones). Running a script prints one line per claim of
the form `X/X`; every script ends with `ALL VALIDATED: True`.

## Requirements

Python 3.8+ and the standard library. Two Part II scripts (`genus.py`, `treewidth.py`) additionally
use [`networkx`](https://networkx.org):

```
pip install -r requirements.txt
```

## Running

Each file is self-contained; run it directly, e.g.

```
python3 dynrank.py
python3 churn.py
python3 twolevers.py
```

## Map to the paper

### Part I — rank-completeness (the SODA content)

| Script            | Validates |
|-------------------|-----------|
| `ph_predictions.py` | Shared library: simplicial complexes, F₂ homology and boundary rank, Vietoris–Rips, discrete Morse matchings, pair-digraphs. |
| `dynrank.py`      | **Main theorem** (dynamic β₁ ≡ dynamic F₂-rank): the crux identity `dim Z₂(K(A)) = k − rank A`, the β₁-recovery formula, entry-flip locality (**exactly 11 triangle toggles**), the suspension identity, and the switched crux + OuMv primitive. |
| `churn.py`        | **The escape**: low-rank churn (`rank(∂ᴹ′ − ∂ᴹ) ≤ |B| = O(δ)`), the Schur/bordering identity, field-independence over F₃/F₅, the Euler obstruction `χ(K(A)) = 2k − nnz`, and the four-rank persistent-Betti formula behind the treewidth maintenance. |
| `twolevers.py`    | The two levers closing Open Problem 1: **bounded-degree hardness** (dynamic rank is OuMv-hard at weight ≤ 3, via the bordered-inverse probe, chain encoding, sparse gluing, and isolation boost) and the **treewidth algorithm** (segment tree of Schur complements), plus the bounded-degree Euler obstruction `χ(Kₛ) = 2 − nnz`. |
| `gadgets.py`      | Auxiliary gadget experiments. |

### Part II — certified-repair theory (the full/arXiv version)

| Script                 | Validates |
|------------------------|-----------|
| `hardness.py`          | Repair = Directed Feedback Vertex Set; NP-hardness for dimension ≥ 2. |
| `dynamic.py`           | Warm-start locality: the prediction error is edit-bounded (η ≤ ⌊δ/2⌋) and edit-local. |
| `dynamic_sequence.py`  | End-to-end warm-start scheme on a changing filtration. |
| `incremental.py`       | The incremental certified-matching data structure (edit-local per-edit cost). |
| `experiment.py`        | Consistency/robustness experiments. |
| `morse_vineyards.py`   | Output-sensitive vineyards via a certified Morse matching. |
| `multiparameter.py`    | The lift to multiparameter persistence. |
| `genus.py`             | The bounded-genus repair bound. |
| `treewidth.py`         | The treewidth bound for repair. |
| `learnability.py`      | Learnability of the prediction error η. |
| `approx.py`            | The filtration-aware result beyond DFVS. |

All scripts pass end-to-end.
