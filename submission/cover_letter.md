# Cover letter (primary version)

Dear Editor-in-Chief,

Please consider the enclosed manuscript, "Dynamic Betti Numbers Are Equivalent to Dynamic Sparse Matrix Rank", for publication in ACM Transactions on Algorithms.

Persistent homology is increasingly applied to data that change over time, but for general complexes of dimension two
or more every known method for updating Betti numbers or barcodes after a single simplex insertion or deletion takes
time polynomial in the size of the complex in the worst case. The manuscript explains why. Its main theorem is an
equivalence: maintaining the first Betti number of a 2-complex under simplex insertions and deletions and maintaining
the rank of a sparse matrix under entry updates reduce to each other with constant overhead (over F_2, and over every
field for matrices with entries in {0, +1, -1}). The reduction rests on a local and switchable gadget, adapted from a
static construction of Edelsbrunner and Parsa, in which an entry flip costs seven simplex updates and switching a row
or column on or off costs one.

Two kinds of consequences follow.

- Lower bounds. Under the OMv conjecture, no data structure with polynomial preprocessing time maintains any Betti
  number beta_p (p >= 1) with amortized update time n^{1/2-eps} and query time n^{1-eps}. The bound holds over every
  field. It also holds for persistent Betti numbers and barcodes under function-value updates, for online zigzag
  persistence, on complexes of bounded degree, on 2-complexes linearly embedded in R^4, for clique and Vietoris-Rips
  complexes of changing metric spaces and of changing point sets in R^{O(log n)}, and even for deciding whether
  the first homology group vanishes. Under the hinted conjecture of van den Brand, Nanongkai, and Saranurak, it becomes a worst-case bound of
  n^{alpha/2-o(1)} over every field, where alpha/2 >= 5/8 and alpha/2 is about 0.703 for the current bounds on matrix
  multiplication.
- Algorithms. Every dynamic-rank algorithm transfers to Betti numbers. In addition, all Betti numbers of subcomplexes
  of any fixed complex linearly embedded in R^3 can be maintained in O(log^2 n) amortized time per update, through
  a combinatorial form of Alexander duality and dynamic connectivity, so maintaining Betti numbers is easy in three dimensions, whereas for
  2-complexes in R^4 it is as hard as maintaining the rank of a sparse 0/1 matrix (and equivalent to it over F_2); this is the dynamic counterpart of the static picture of Edelsbrunner and Parsa
  (SODA 2014). Without geometry, bounded treewidth of the Hasse diagram of the complex suffices for polylogarithmic
  worst-case updates, unconditionally.

The work connects dynamic algorithms, fine-grained complexity, and computational topology, and I believe it will
interest TALG readers in all three areas. All proofs are complete and appear in the body of the paper. The
combinatorial identities used in the proofs were also checked by brute-force computation, and the code is
available as supplementary material.

A preliminary version is available as an arXiv preprint. The manuscript has not been published, and it is not under
consideration at any other venue.

Sincerely,
Shawn Ray
Carnegie Mellon University

---

# Alternative paragraph (use only if you want to disclose the earlier conference submission)

An earlier version of this work was submitted to SODA 2027. The reviewers found the results interesting and the
gadget elegant, but found the presentation hard to follow. This manuscript was rewritten from scratch in response.
Every concept is defined before it is used, theorem statements contain only mathematics, every proof is complete
and sits next to its statement, and amortized and worst-case bounds are kept separate. The hinted worst-case bounds
of van den Brand, Nanongkai, and Saranurak are now discussed explicitly, related work (including Dey, Hou, and
Parsa, WADS 2023) is positioned precisely, and the experimental section was removed. Several results are new in this
version: the dichotomy between three and four dimensions, and the lower bounds for Vietoris-Rips complexes, online
zigzag persistence, deciding whether homology vanishes, and partially dynamic data structures.
