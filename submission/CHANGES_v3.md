# What changed from paper-v2 to paper-v3

paper-v3 was produced by three coordinated sessions (front matter and integration; proofs; figures and layout).
Each pass was checked against simulated TALG referees and independent proof audits.

## Venue
- ACM Transactions on Algorithms, kept after re-checking the alternatives (see `SUBMISSION.md`). Submissions are
  year-round, there is no page limit, and no talk or video is required.

## New or strengthened results
- **Bounded treewidth suffices** (new; resolves an open problem of v2). Given a tree decomposition of width t of the
  Hasse diagram, every Betti number is maintained with O((t+1)^3 log n log(t+2)) field operations per update, in the
  worst case, deterministically. This comes from a general column-hierarchy rank structure. It is verified by brute
  force (`verification/hierarchy.py`) and by an independent adversarial audit.
- **Worst-case (hinted) lower bound now holds over every field**, including F_2 (v2: characteristic zero only). Its
  exponent is stated correctly as n^{α/2−o(1)}, with α/2 ≥ 5/8, and α/2 ≈ 0.703 under the current bounds on matrix
  multiplication.
- **Clique and Vietoris–Rips complexes**: hardness for every β_p (p ≥ 1), under vertex, edge, distance (metric
  spaces), and point updates.
- **Explicit barcode maintenance and output-sensitive algorithms** are excluded. The bound also holds in the
  current complex size |K|.
- **The OMv bound is factored explicitly** through a new Lemma (dynamic rank with switches is OuMv-hard). This
  answers SODA reviewer B's question "why is Thm 3 not a consequence of Thm 2".
- **Unconditional Ω(log n) cell-probe bound** (Pătraşcu–Demaine) for every β_p, so the polylogarithmic algorithms
  are optimal up to a logarithmic factor.
- **Duality explanation of the 3D/4D line**: for subcomplexes of S^d, duality determines everything for d = 3, but
  for d = 4 it leaves exactly β_1 and β_2 undetermined.

## Presentation
- **Retitled** from "Maintaining Betti Numbers Is Exactly as Hard as Maintaining Matrix Rank" to "Dynamic Betti Numbers
  Are Equivalent to Dynamic Sparse Matrix Rank". Several simulated referees flagged "exactly", because the
  equivalence holds up to constant factors in the sparse size measure, and for {0,±1} matrices over general fields.
- Abstract rewritten. Every quantifier is stated (polynomial preprocessing, general complexes, worst case), and the
  scope of the equivalence ({0,±1} matrices over general fields) appears immediately.
- Introduction restructured:
  - the OMv conjecture is stated in plain words;
  - Theorem 1.1 gives both directions of the equivalence;
  - robustness results appear as a list;
  - Theorem 1.3 states the 3D/4D dichotomy;
  - the technical overview derives the exponents 1/2 and 1 and sketches the almost-acyclic construction;
  - the landscape table was redesigned.
- Three new figures: the gadget (Fig. 1, redesigned), the complexity landscape (Fig. 2), and the roadmap of results
  (Fig. 3). Further figures in the body: socket, OuMv, bounded degree, open book, duality.
- The ℝ⁴ hardness proof moved from "easy cases" into the lower-bound section. The algorithms section was retitled.
- Notation clashes removed. The tether is now Λ_j, the suspension Susp, and the number of independent cycles of the
  1-skeleton β_1(U^{(1)}). Orientation conventions, the word-RAM model, and amortization with interleaved queries
  are defined.
- Verification code moved out of the narrative into a short "Supplementary material" note.

## Accuracy and related work
- All 49 original references verified, plus every new one. Fixes:
  - ω is attributed to Alman et al.;
  - Dey–Hou–Parsa's technique (dynamic trees) is described correctly;
  - banana trees use the augmented diagram;
  - Fomin et al. need a given tree decomposition;
  - KM26 is cited in its ICALP 2026 version.
- Edelsbrunner–Parsa is described accurately: an unspecified O(p) cap triangulation, a pencil embedding (credited),
  sparsification, and prime fields. The contribution is stated precisely: switches give the basic OMv bound,
  socket locality gives the equivalence, and the orientation analysis covers every field.
- New related work: Ding–Kyng–Probst Gutenberg–Zhang and Kyng–Zhang (static completeness of 2-complex operators),
  Black–Nayyeri (ℝ³ Laplacian solvers), Piekenbrock–Perea, annotations, Kerber–Schreiber, Maria–Oudot,
  Wiedemann/Kaltofen–Saunders, Yuster, Larsen–Williams, Pătraşcu–Demaine.
- Overclaims removed: "explains the gap", "sublinear ... requires structure", "maintaining homology is easy in
  three dimensions", "what our gadget adds is sparsity".
