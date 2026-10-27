/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part12
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

/-!
### Canonical (Deterministic) Intersection Data Selection

To prove that signReversing is an involution, we need to select intersection data
(i, j, v) deterministically so that the same selection is made before and after
applying the involution.

The canonical selection algorithm:
1. i = smallest index in crowdedPathIndices (using Finset.min')
2. v = first crowded vertex on path i (by position in the path)
3. j = largest index in pathIndicesContaining v, excluding i (using Finset.max')

This selection is preserved under exchangeTails because:
- The head of path i (vertices before v) is unchanged
- So v is still the first crowded vertex on path i
- And j is still the largest index containing v
-/

/-- A crowded path index has at least 2 paths containing some crowded vertex -/
theorem PathTuple.crowdedPathIndex_pathIndicesContaining_card {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices)
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i) :
    1 < (pt.pathIndicesContaining v).card := by
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  obtain ⟨hvi, j, hij, hvj⟩ := hv
  have hi_mem : i ∈ pt.pathIndicesContaining v := by
    simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvi
  have hj_mem : j ∈ pt.pathIndicesContaining v := by
    simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvj
  have hne : i ≠ j := hij
  calc (pt.pathIndicesContaining v).card 
      ≥ ({i, j} : Finset (Fin k)).card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hi_mem
        · exact hj_mem)
    _ = 2 := by simp [hne]
    _ > 1 := by omega

/-- If i is a crowded path index, the set of other path indices containing a crowded vertex on i
    is nonempty -/
theorem PathTuple.pathIndicesContaining_sdiff_singleton_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices)
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i) :
    (pt.pathIndicesContaining v \ {i}).Nonempty := by
  have hcard := pt.crowdedPathIndex_pathIndicesContaining_card i hi v hv
  rw [Finset.sdiff_nonempty]
  intro h
  have hsub : pt.pathIndicesContaining v ⊆ {i} := h
  have : (pt.pathIndicesContaining v).card ≤ ({i} : Finset (Fin k)).card := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

/-- A crowded path index has nonempty crowdedVerticesOnPath -/
theorem PathTuple.crowdedPathIndex_crowdedVerticesOnPath_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    (pt.crowdedVerticesOnPath i).Nonempty := by
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨j, hij, v, hv⟩ := hi
  simp only [Finset.mem_inter, List.mem_toFinset] at hv
  use v
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hv.1, j, hij, hv.2⟩

/-- The first crowded vertex on path i (when i is a crowded path index) exists in the path -/
theorem PathTuple.firstCrowdedIndexOnPath_lt_length {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    pt.firstCrowdedIndexOnPath i < (pt.paths i).vertices.length := by
  have hne := pt.crowdedPathIndex_crowdedVerticesOnPath_nonempty i hi
  obtain ⟨v, hv⟩ := hne
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  unfold firstCrowdedIndexOnPath
  apply List.findIdx_lt_length_of_exists
  use v, hv.1
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq]
  exact hv

/-- The vertex at firstCrowdedIndexOnPath is in crowdedVerticesOnPath -/
theorem PathTuple.firstCrowdedVertex_mem_crowdedVerticesOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    let idx := pt.firstCrowdedIndexOnPath i
    let h := pt.firstCrowdedIndexOnPath_lt_length i hi
    (pt.paths i).vertices.get ⟨idx, h⟩ ∈ pt.crowdedVerticesOnPath i := by
  simp only
  unfold firstCrowdedIndexOnPath
  have h_lt := pt.firstCrowdedIndexOnPath_lt_length i hi
  unfold firstCrowdedIndexOnPath at h_lt
  have h_findIdx := @List.findIdx_getElem _ (fun v => v ∈ pt.crowdedVerticesOnPath i) 
    (pt.paths i).vertices h_lt
  simp only [List.get_eq_getElem]
  simp at h_findIdx
  exact h_findIdx

end LGV
