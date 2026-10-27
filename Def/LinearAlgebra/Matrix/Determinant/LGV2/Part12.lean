/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part10
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

noncomputable def PathTuple.maxOtherPathIndex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Fin k :=
  (pt.otherPathsContainingFirstCrowded hip).max' (pt.otherPathsContainingFirstCrowded_nonempty hip)

/-- Helper function to extract intersection indices from an intersecting path tuple.
    Returns a pair (i, j) with i ≠ j such that paths i and j intersect. -/
noncomputable def getIntersectionIndices {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { p : Fin k × Fin k // p.1 ≠ p.2 } :=
  Classical.choice (by
    -- Convert isIntersecting to existential form using isIntersecting_iff_exists_crowded
    rw [PathTuple.isIntersecting_iff_exists_crowded] at hip
    obtain ⟨v, i, j, hij, _, _⟩ := hip
    exact ⟨⟨(i, j), hij⟩⟩)

/-- Helper function to extract full intersection data from an intersecting path tuple.
    Returns (i, j, v, hvi, hvj) where i ≠ j and v is on both paths i and j. -/
noncomputable def getIntersectionData {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { data : (i : Fin k) × (j : Fin k) × { v : V // v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices } // 
      data.1 ≠ data.2.1 } :=
  Classical.choice (by
    rw [PathTuple.isIntersecting_iff_exists_crowded] at hip
    obtain ⟨v, i, j, hij, hvi, hvj⟩ := hip
    exact ⟨⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩⟩)

end LGV
