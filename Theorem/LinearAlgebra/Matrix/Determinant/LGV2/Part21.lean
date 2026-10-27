/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part24
open Finset BigOperators Matrix

/-!
# The Lindström-Gessel-Viennot Lemma: Weighted and Generalized Versions

This file formalizes the weighted version of the LGV lemma and related results,
following Section "The weighted version ... The nonpermutable case" (sec.det.comb.lgv)
of the Algebraic Combinatorics notes.

## Main definitions

* `LGV.SimpleDigraph`: A digraph structure with no self-loops (irreflexive adjacency)
* `LGV.SimpleDigraph.toDigraph`: Conversion to Mathlib's `Digraph` type
* `LGV.ArcWeight`: A weight function on arcs of a digraph
* `LGV.pathWeight`: The weight of a path (product of arc weights)
* `LGV.pathTupleWeight`: The weight of a path tuple (product of path weights)
* `LGV.pathWeightMatrix`: The matrix of sums of path weights between source/target vertices
* `LGV.catalanHankelMatrix`: The Hankel matrix of Catalan numbers

## Main results

* `LGV.lgv_weighted_lattice`: LGV lemma, lattice weight version (Theorem thm.lgv.kpaths.wt)
* `LGV.lgv_weighted_digraph`: LGV lemma, digraph weight version (Theorem thm.lgv.kpaths.wt-dg)
* `LGV.lgv_nonpermutable`: LGV lemma, nonpermutable lattice weight version
    (Corollary cor.lgv.kpaths.wt-np)
* `LGV.binom_det_nonneg`: Determinant of binomial coefficient matrix is nonnegative
    (Corollary cor.lgv.binom-det-nonneg)
* `LGV.catalan_hankel_det`: Hankel determinant of Catalan numbers equals 1
    (Corollary cor.lgv.catalan-hankel-det-0)
* `LGV.catalan_hankel_det_zero` through `LGV.catalan_hankel_det_seven`: Base cases proved
    by computation

## References

* Source: AlgebraicCombinatorics/tex/Determinants/LGV2.tex
* [Lindström, *On the vector representations of induced matroids*][Lindstrom73]
* [Gessel-Viennot, *Binomial determinants, paths, and hook length formulae*][GesVie85]

## Implementation notes

We formalize the LGV lemma for general path-finite acyclic digraphs, with the integer
lattice ℤ² as a special case. The key construction is a sign-reversing involution
on intersecting path tuples that exchanges tails at the first intersection point.

The nonpermutable case applies when the source and target vertices are "sorted" in
a way that prevents non-identity permutations from having non-intersecting path tuples.

For the Catalan Hankel determinant, we use Mathlib's `catalan` function and prove
the base cases (k = 0, 1, ..., 7) by direct computation using `native_decide`.
The general theorem uses the LGV lemma with Dyck paths.

### Relationship with LGV1.lean

This file (LGV2.lean) and LGV1.lean both work with the integer lattice digraph, but
use different representations:

- **LGV1.lean**: Uses Mathlib's `Digraph` type and `LatticePath` (list of steps: east/north)
- **LGV2.lean**: Uses `LGV.SimpleDigraph` (custom structure with irreflexivity) and
  `SimpleDigraph.Path` (list of vertices)

The integer lattice definitions have equivalent adjacency relations, proven by
`integerLattice_arc_iff` and `integerLattice_toDigraph_adj_iff`. The conversion
`SimpleDigraph.toDigraph` allows transferring results between the two representations.

This file contains the complete weighted LGV lemma proof. LGV1.lean contains the
counting case infrastructure with lattice-specific path counting results.
-/


namespace LGV

variable {V : Type*} [DecidableEq V] {K : Type*} [CommRing K]

variable {V : Type*} [DecidableEq V]

/-- The vertices list is nonempty -/
theorem LatticePath'.toVertices_nonempty (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start) ≠ [] := by
  cases path <;> simp [toVertices]

/-- Each step creates a valid arc in the integer lattice -/
theorem LatticeStep'.apply_creates_arc (s : LatticeStep') (p : ℤ × ℤ) :
    integerLattice.arc p (s.apply p) := by
  cases s with
  | east => 
    simp only [apply, integerLattice]
    left
    simp
  | north => 
    simp only [apply, integerLattice]
    right
    simp

/-- Consecutive vertices in toVertices are connected by arcs -/
theorem LatticePath'.toVertices_arcs_valid (path : LatticePath') (start : ℤ × ℤ) :
    ∀ i : ℕ, ∀ hi : i + 1 < (LatticePath'.toVertices path start).length,
      integerLattice.arc ((LatticePath'.toVertices path start).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((LatticePath'.toVertices path start).get ⟨i + 1, hi⟩) := by
  induction path generalizing start with
  | nil => intro i hi; simp [toVertices] at hi
  | cons s rest ih =>
    intro i hi
    simp only [toVertices] at hi ⊢
    cases i with
    | zero =>
      simp only [List.get_eq_getElem, List.getElem_cons_zero,
                 List.getElem_cons_succ]
      cases rest with
      | nil =>
        simp only [toVertices, List.getElem_singleton]
        exact LatticeStep'.apply_creates_arc s start
      | cons s' rest' =>
        simp only [toVertices, List.getElem_cons_zero]
        exact LatticeStep'.apply_creates_arc s start
    | succ j =>
      simp only [List.get_eq_getElem, List.getElem_cons_succ] at hi ⊢
      simp only [List.length_cons] at hi
      exact ih (s.apply start) j (by omega : j + 1 < (LatticePath'.toVertices rest (s.apply start)).length)

end LGV
