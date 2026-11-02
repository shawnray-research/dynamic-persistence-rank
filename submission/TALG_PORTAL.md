# TALG portal fields (copy and paste)

## Type
Original Article

## Title (45 of 50 characters)
Dynamic Betti Numbers and Dynamic Matrix Rank

The full title, "Dynamic Betti Numbers Are Equivalent to Dynamic Sparse Matrix Rank" (67 characters), exceeds the
portal's 50-character limit. The portal title above is the paper's own short title (`\title[...]` in `paper/main.tex`),
which also appears in the PDF's running heads.

## Abstract (245 of 250 words, plain text)
For general complexes of dimension two or more, every known method for updating persistent homology after inserting or deleting a single simplex takes worst-case time polynomial in the number n of simplices. We show that, over the two-element field, maintaining the first Betti number of a 2-complex under simplex insertions and deletions and maintaining the rank of a sparse matrix under entry updates reduce to each other with constant overhead per operation; over every field, the same holds for matrices with entries in {0,±1}. The key ingredient is a gadget, adapted from a static construction of Edelsbrunner and Parsa, in which switching a row or column costs one simplex update and each entry update a constant number. Under the Online Matrix-Vector multiplication (OMv) conjecture, no data structure with polynomial preprocessing time can maintain a Betti number β_p, p ≥ 1, of a subcomplex of a fixed complex with n simplices in amortized time O(n^{1/2−ε}) per update and O(n^{1−ε}) per query, for any ε > 0. This holds over every field and extends to persistent Betti numbers under function-value updates, online zigzag persistence, complexes of bounded degree, 2-complexes linearly embedded in R^4, and Vietoris–Rips complexes of changing metric spaces and of changing point sets in R^{O(log n)}; it applies even to deciding whether the first homology group vanishes. In contrast, all Betti numbers of subcomplexes of a fixed complex linearly embedded in R^3 can be maintained in O(log^2 n) amortized time per update after polynomial-time preprocessing.

This is a shortened version of the abstract in the PDF (344 words), which exceeds the portal limit.

## Attributes: ACM CCS 2012 (Step 3, one per "Add"; these match `\ccsdesc` in `paper/main.tex`)
Theory of computation~Computational geometry
Theory of computation~Data structures design and analysis
Theory of computation~Problems, reductions and completeness
Mathematics of computing~Algebraic topology
