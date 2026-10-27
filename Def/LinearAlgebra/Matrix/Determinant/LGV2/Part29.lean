/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part25
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

/-- The vertices visited by a path in a LatticePath'Tuple -/
def LatticePath'Tuple.verticesOf {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) (i : Fin k) : Set (ℤ × ℤ) :=
  { p | p ∈ LatticePath'.toVertices (pt.paths i) (A i) }

/-- A LatticePath'Tuple is non-intersecting if no two paths share a vertex -/
def LatticePath'Tuple.isNonIntersecting {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) : Prop :=
  ∀ i j, i ≠ j → Disjoint (pt.verticesOf i) (pt.verticesOf j)

/-- A LatticePath'Tuple is intersecting if it is not non-intersecting -/
def LatticePath'Tuple.isIntersecting {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) : Prop :=
  ¬pt.isNonIntersecting

/-- Convert a LatticePath'Tuple to a PathTuple -/
noncomputable def latticePath'TupleToPathTuple {k : ℕ} {A B : kVertex (ℤ × ℤ) k}
    (pt : LatticePath'Tuple k A B) : PathTuple integerLattice k A B where
  paths := fun i => LatticePath'.toPath (pt.paths i) (A i)
  starts := fun i => LatticePath'.toPath_start (pt.paths i) (A i)
  finishes := fun i => by
    rw [LatticePath'.toPath_finish]
    exact pt.valid i

/-- Convert a PathTuple to a LatticePath'Tuple -/
noncomputable def pathTupleToLatticePath'Tuple {k : ℕ} {A B : kVertex (ℤ × ℤ) k}
    (pt : PathTuple integerLattice k A B) : LatticePath'Tuple k A B where
  paths := fun i => pathToLatticePath' (pt.paths i)
  valid := fun i => by
    have h := verticesToSteps'_toVertices (pt.paths i).vertices (pt.paths i).nonempty (pt.paths i).arcs_valid
    have hstart : (pt.paths i).start = A i := pt.starts i
    have hfinish : (pt.paths i).finish = B i := pt.finishes i
    simp only [SimpleDigraph.Path.start] at hstart
    simp only [SimpleDigraph.Path.finish] at hfinish
    unfold pathToLatticePath'
    -- The endpoint is computed by foldl, which equals the last vertex
    have h_toVertices : LatticePath'.toVertices (verticesToSteps' (pt.paths i).vertices (pt.paths i).arcs_valid) 
        ((pt.paths i).vertices.head (pt.paths i).nonempty) = (pt.paths i).vertices := h
    rw [hstart] at h_toVertices
    have h_endpoint : LatticePath'.endpoint (verticesToSteps' (pt.paths i).vertices (pt.paths i).arcs_valid) (A i) =
        ((pt.paths i).vertices.getLast (pt.paths i).nonempty) := by
      rw [← LatticePath'.toVertices_getLast]
      simp only [h_toVertices]
    unfold LatticePath'.endpoint at h_endpoint ⊢
    rw [h_endpoint, hfinish]

/-- The bijection between LatticePath'Tuple and PathTuple -/
noncomputable def latticePath'TupleEquiv {k : ℕ} (A B : kVertex (ℤ × ℤ) k) :
    LatticePath'Tuple k A B ≃ PathTuple integerLattice k A B where
  toFun := latticePath'TupleToPathTuple
  invFun := pathTupleToLatticePath'Tuple
  left_inv pt := by
    apply LatticePath'Tuple.ext
    intro i
    simp only [pathTupleToLatticePath'Tuple, latticePath'TupleToPathTuple]
    -- Need to show: pathToLatticePath' (LatticePath'.toPath (pt.paths i) (A i)) = pt.paths i
    have h := LatticePath'.toPath_injective (A i)
    apply h
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices (LatticePath'.toVertices (pt.paths i) (A i)) 
      (LatticePath'.toVertices_nonempty (pt.paths i) (A i)) 
      (LatticePath'.toVertices_arcs_valid (pt.paths i) (A i))
    simp only [LatticePath'.toVertices_head] at this
    exact this
  right_inv pt := by
    apply PathTuple.ext
    intro i
    simp only [latticePath'TupleToPathTuple, pathTupleToLatticePath'Tuple]
    -- Need to show: LatticePath'.toPath (pathToLatticePath' (pt.paths i)) (A i) = pt.paths i
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices (pt.paths i).vertices (pt.paths i).nonempty (pt.paths i).arcs_valid
    have hstart : (pt.paths i).start = A i := pt.starts i
    simp only [SimpleDigraph.Path.start] at this hstart
    rw [hstart] at this
    exact this

end LGV
