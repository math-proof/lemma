/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part18
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

/-- Convert a DyckWord to a Dyck path from (0, 0) to (2n, 0) where n = semilength.

    **Note:** The vertices are constructed as (i, y_i) where y_i = #U - #D in the first i steps.
    The Dyck word conditions ensure y_i ≥ 0 and the path stays in the valid region. -/
def dyckWordToPath (w : DyckWord) : SimpleDigraph.Path dyckDigraph where
  vertices := dyckWordToVertices w
  nonempty := dyckWordToVertices_nonempty w
  arcs_valid := by
    intro i hi
    rw [dyckWordToVertices_length] at hi
    have hi' : i < w.toList.length := by omega
    have hi1 : i + 1 < (dyckWordToVertices w).length := by rw [dyckWordToVertices_length]; omega
    have hi0 : i < (dyckWordToVertices w).length := by omega
    simp only [List.get_eq_getElem]
    rw [dyckWordToVertices_getElem w i hi0, dyckWordToVertices_getElem w (i + 1) hi1]
    have hstep : w.toList[i] = DyckStep.U ∨ w.toList[i] = DyckStep.D := DyckStep.dichotomy _
    unfold dyckWordY
    have htake_succ : w.toList.take (i + 1) = w.toList.take i ++ [w.toList[i]] := by
      rw [List.take_succ_eq_append_getElem hi']
    rcases hstep with hU | hD
    · -- U step: y increases by 1
      left
      constructor
      · push_cast; ring
      · rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton]
        simp only [hU]
        have h1 : (if (DyckStep.U == DyckStep.U) = true then 1 else 0) = 1 := by native_decide
        have h2 : (if (DyckStep.U == DyckStep.D) = true then 1 else 0) = 0 := by native_decide
        simp only [h1, h2, add_zero]
        have hle := w.count_D_le_count_U i
        omega
    · -- D step: y decreases by 1
      right
      constructor
      · push_cast; ring
      constructor
      · rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton]
        simp only [hD]
        have h1 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
        have h2 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
        simp only [h1, h2, add_zero]
        have hle := w.count_D_le_count_U i
        have hle' := w.count_D_le_count_U (i + 1)
        rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton] at hle'
        simp only [hD, h1, h2, add_zero] at hle'
        omega
      · exact dyckWord_y_pos_before_D w i hi' hD

/-- Translation function for vertices in the Dyck digraph -/
def translateVertex (d : ℤ) (v : ℤ × ℕ) : ℤ × ℕ := (v.1 + d, v.2)

end LGV
