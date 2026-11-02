# Dynamic Betti Numbers Are Equivalent to Dynamic Sparse Matrix Rank

LaTeX source, compiled PDF, and computer verification for the paper

> **Dynamic Betti Numbers Are Equivalent to Dynamic Sparse Matrix Rank**
> Shawn Ray. Prepared for submission to *ACM Transactions on Algorithms* (TALG). Branch `paper-v3` holds the current version.

**PDF:** [`dynamic-betti-rank.pdf`](dynamic-betti-rank.pdf)

## Results in one paragraph

Maintaining a Betti number of a simplicial complex under single-simplex insertions and deletions and maintaining
the rank of a sparse matrix under entry updates reduce to each other with constant overhead (over F₂; over every
field for matrices with entries in {0, ±1}). The reduction from rank to homology is a local, switchable version of
the static gadget of Edelsbrunner and Parsa: an entry flip costs 7 simplex updates and switching a row or column on
or off costs 1. Consequently, under the OMv conjecture, no data structure maintains β_p (p ≥ 1) with amortized update
time O(n^{1/2−ε}) and query time O(n^{1−ε}). The bound holds over every field and persists for persistent Betti
numbers under value updates, online zigzag persistence, bounded-degree complexes, 2-complexes linearly embedded in
R⁴, clique complexes and Vietoris–Rips complexes of changing point sets (in R^{O(log n)}) and metric spaces,
partially dynamic (worst-case) data structures, and even for deciding whether H₁ vanishes. Under the uMv-hinted
conjecture of van den Brand, Nanongkai, and Saranurak, worst-case update or query time n^{α/2−o(1)} is necessary
over every field (α/2 ≥ 5/8, and α/2 ≈ 0.703 with current matrix-multiplication bounds), while every dynamic-rank
algorithm transfers (randomized O(n^{1.407}) per update).
In contrast, all Betti numbers of subcomplexes of any fixed geometric complex in R³ can be maintained in O(log² n)
amortized time after polynomial preprocessing (easy in three dimensions, hard in four), and every Betti number of a
universe whose Hasse diagram has treewidth t can be maintained with O((t+1)³ log n log(t+2)) field operations per
update in the worst case, unconditionally.

## Repository layout

| Path | Contents |
|------|----------|
| [`dynamic-betti-rank.pdf`](dynamic-betti-rank.pdf) | The compiled paper. |
| [`paper/`](paper/) | LaTeX source (`main.tex`; ACM `acmart` class, `acmsmall` format) and bibliography. |
| [`verification/`](verification/) | Brute-force checks of the combinatorial identities used in the proofs (table below). |
| [`submission/`](submission/) | TALG submission notes and a cover-letter draft. |
| [`legacy/`](legacy/) | Verification scripts of the earlier, longer version of this work (kept for reference; not used by the current paper). |

## Building the paper

```
cd paper
latexmk -pdf main.tex        # or: tectonic main.tex (no local TeX installation needed)
```

## Verification

The scripts are **not part of any proof**. They check, by brute-force homology computations (ranks of boundary
matrices over F₂, and over F₃, F₅, F₇ with oriented boundary matrices where noted), the combinatorial identities
used in the proofs, exhaustively on small instances and randomly on larger ones. Every script uses only the standard
library of Python 3.8 or later, is self-contained, and ends with `ALL VALIDATED: True`:

```
cd /tmp && python3 -I /path/to/verification/<script>.py
```

| Script | Paper statement | What is checked |
|---|---|---|
| `paper_complex.py` | Definition of the gadget; Lemma (Crux); Eq. (β₁ from β₂); signed entries | The exact complex of the definition (all edges of the universe present, tethers, general admissible sets P): β₂(K(A;R,J)) = \|J\| − rk A[R,J] and β₁ = c_U + β₂ − n₂ over F₂, F₃, F₅, F₇ (1052 random and edge cases), **exhaustively** for all P, A, R, J with (r,k) ≤ (2,2), (3,1), (1,3) over F₂ and F₃ (4642 cases), and for entries in {0, ±1} with reversed tubes (360 cases). |
| `hole_gadget.py` | Lemma (Locality); switches | An entry flip changes exactly 7 triangles; switches are single triangles; β₂ = \|J\| − rk A[R,J] and the Boolean OuMv identity. |
| `fields.py` | Lemma (Crux) over other fields | Crux identity over F₃ and F₅ with signed boundary matrices, including matrices whose rank would change under a non-uniform sign pattern. |
| `orientation.py` | Orientation argument of Section 4.3 | ∂Cyl(a,b) = [a] − [b], ∂Cyl°(a,b) = [a] − [b] − [h], ∂Cyl(h,c) = [h] − [c], the cone orientations, the column identity ∂[Σ_j] = −[P_j] − Σ A_ij [C_i], and coherence. |
| `signed.py` | Equivalence over every field for entries in {0, ±1} | Reversed tubes: dim Z₂ = \|J\| − rank A[R,J] over F₃ and F₅ for A ∈ {0, ±1} (240 cases); update costs 7 or 8 triangles. |
| `bdeg.py` | Bounded-degree gadget; Theorem (bounded degree); Corollary (sparse rank) | Chain-of-copies universe: crux identity over F₂ (exhaustive for ℓ ≤ 2), F₃, F₅; OuMv identity; ≤ 3 triangles per edge and ≤ 23 simplices per vertex; flip = 7 triangles, switch = 1. |
| `s3.py` | Lemma (dual graph); Theorem (3-sphere) | Nine triangulated 3-spheres, 315 random subcomplexes, and 4374 dynamic operations compared with brute force after every operation; F₃/F₅ agreement; wrong formula variants are detected. |
| `r4.py` | Theorem (embedding in R⁴) | Explicit open-book coordinates: every pair of simplices meets properly (exact rational LPs); negative controls are detected. |
| `anyR3.py` | Corollary anyR3 (every fixed geometric complex in R³) | The compressed dual graph: for universes U that are proper subcomplexes of triangulated 3-spheres, β₃(K) = 0 and β₂(K) = c(G(K)) − n₃(K) − 1, where G(K) has the outer cells and the tetrahedra of U as nodes and one edge per triangle of U not in K (1440 random (U, K) pairs, 367 with β₂ > 0). |
| `threshold.py` | Remark threshold (two nonzeros per column is easy) | For A ∈ {0, ±1}^{r×k} with at most two nonzeros per column: rank_F A[R,J] = \|R\| − c(Γ̃) + c(Γ) over F₂, F₃, F₅ (600 random instances). |
| `easy_checks.py` | Section 6: Lemma (dual graph), Theorem (3-sphere), Theorem (width), Corollary (bandwidth), Lemma (column) | Duality formulas on further triangulated 3-spheres over F₂, F₃, F₅; the segment-tree summaries of the width algorithm against direct rank computations; the bandwidth bound; exact rational checks of the column model used in the R⁴ embedding. |
| `misc_identities.py` | χ(K(A)), β₁(K(A)), four-rank formula, Alexander duality | χ(K(A)) = 2k − nnz; β₁(K(A)) = (r − rk A) + (nnz − r − k + c(G_A)); four-rank formula for persistent Betti numbers; duality on a triangulated S³. |
| `acyclic.py`, `acyclic_hole_gadget.py` | Theorem (deciding whether H₁ vanishes) and its lemmas | Coned lean complex has (β₀, β₁, β₂) = (1, r − rk A, k − rk A); bordered instance has β₁ = β₂ = [uᵀMv = 0]; isolation probability ≥ 1/4 (exactly 1/4 in the worst case). |
| `hinted_check.py` | Corollary (worst-case lower bound) | The bordered-inverse identity for the five-matrix product over Q: rank_Q of the bordered 0/1 block-unitriangular matrix equals m + [Boolean product entry = 1] (exact rational arithmetic). |
| `flag_rips.py` | Theorem (clique and Vietoris–Rips complexes) | The clique complex of the induced comparability graph is sd(K) with the same Betti numbers; constant maximum degree of the comparability graph of the bounded-degree universe. |
| `hierarchy.py` | Theorem (column hierarchy), Lemma (merge), Corollary (treewidth) | Random column hierarchies over F₂, F₃, F₅, F₇ (240 matrices, 40 random switches each), and hierarchies built from random tree decompositions as in the proof of the treewidth corollary (214 instances). Checks Lemma merge (a) and (b) at every node and the width bound Δ(t+1), and compares the maintained rank with a direct rank computation after every switch. |
| `hinted_masks.py` | Corollary (worst-case lower bound) | Random 0/1 masks of M1, M3, M5: a masked product entry is 0 when the Boolean entry is 0, and nonzero for at least 1/8 of all masks when it is 1 (exact enumeration over F2, F3, F5, 108 instances); bordered-rank identity for the block-unitriangular matrix. |
