# Submitting to ACM Transactions on Algorithms (TALG)

**Why TALG.** TALG accepts submissions year-round (no deadline), has no page limit (full proofs stay in the paper),
and requires no talk, video, or rebuttal phase: you submit and wait for the reports. It is the standard journal home
for SODA-style algorithms papers, and its scope ("original research of lasting value on the mathematical aspects of
discrete algorithms") covers dynamic data structures, fine-grained lower bounds, and computational topology.
Alternatives considered and rejected: SoCG 2027 (no call for papers yet; double-blind, 500-line limit, talk in
Bengaluru), ICALP/ESA 2027 (deadlines in 2027), STOC (talk/video), SICOMP/JACM (higher risk), DCG/JACT (narrower
algorithms readership).

**Portal.** ACM Manuscript Central for TALG (linked from https://dl.acm.org/journal/talg/author-guidelines).
**Manuscript.** `dynamic-betti-rank.pdf` (repository root). LaTeX source: `paper/` (acmart, `acmsmall`, review mode
with line numbers, which referees appreciate). Build: `cd paper && latexmk -pdf main.tex`.
**Files to upload.** Exactly the three files in `upload/`; see `upload/UPLOAD.md` for the file designations.
**Article type.** Original Article (portal title and abstract: `TALG_PORTAL.md`).
**Subject areas.** Data structures; lower bounds and fine-grained complexity; computational geometry and topology.
**Cover letter.** `cover_letter.md` (primary version first; an optional paragraph disclosing the SODA history follows).

## Checklist before you press submit
1. Read the PDF once end to end (about 56 pages in review format with line numbers).
2. Replace the arXiv version with this one (new title and abstract below). A current arXiv version is the
   single most effective way to get the paper read and cited, and TALG allows preprints.
3. Upload the three files in `upload/` with the designations in `upload/UPLOAD.md`.
4. Optionally suggest referees (check conflicts and current affiliations first). People who know the relevant areas:
   - computational topology: Salman Parsa, Tamal K. Dey, Tao Hou, Michael Kerber, Ulrich Bauer;
   - dynamic algebraic algorithms and fine-grained complexity: Jan van den Brand, Thatchaphol Saranurak,
     Danupon Nanongkai, Monika Henzinger.

## arXiv metadata (for the replacement)
**Title:** Dynamic Betti Numbers Are Equivalent to Dynamic Sparse Matrix Rank
**Abstract (plain text):**
Persistent homology is increasingly computed on data that change over time, yet for general complexes of dimension
two or more every known method for updating it after the insertion or deletion of a single simplex takes time
polynomial in the number n of simplices in the worst case. We show that this is no accident: for every p ≥ 1,
maintaining the Betti number β_p is equivalent, up to constant factors, to maintaining the rank of a sparse matrix.
Precisely, over the two-element field, the following two problems reduce to each other with constant overhead per
operation: maintaining the first Betti number of a 2-complex under simplex insertions and deletions, and maintaining
the rank of a sparse matrix under entry updates; over every field, the same holds for matrices with entries in
{0,±1}. The key ingredient is a gadget, adapted from a static construction of Edelsbrunner and Parsa, in which
switching a row or column off or on costs one simplex update and every entry update costs a constant number. The
switches alone imply that, under the Online Matrix-Vector multiplication (OMv) conjecture, no data structure with
polynomial preprocessing time can maintain a Betti number β_p, p ≥ 1, of a subcomplex of a fixed complex with n
simplices in amortized time O(n^{1/2−ε}) per update and O(n^{1−ε}) per query, for any ε > 0. This holds over every
field and extends to persistent Betti numbers under function-value updates, online zigzag persistence, complexes of
bounded degree, 2-complexes linearly embedded in R^4, Vietoris–Rips complexes of changing metric spaces and of
changing point sets in R^{O(log n)}, and even to deciding whether the first homology group vanishes. In contrast, all
Betti numbers of subcomplexes of any fixed complex linearly embedded in R^3 can be maintained in O(log² n) amortized
time per update after polynomial-time preprocessing. Maintaining Betti numbers is thus easy for complexes in R^3,
whereas for 2-complexes in R^4 it is as hard as maintaining the rank of a sparse 0/1 matrix, and over the
two-element field equivalent to it.
**Categories:** cs.DS (primary); cs.CG, cs.CC, math.AT (cross-lists).
