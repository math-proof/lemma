/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part18
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

/-- The step list has length = vertices.length - 1 = number of arcs. -/
theorem dyckPathToSteps_length (p : SimpleDigraph.Path dyckDigraph) :
    (dyckPathToSteps p).length = p.vertices.length - 1 := by
  simp [dyckPathToSteps]

/-- Key lemma: the y-coordinate at position i equals #U - #D in the first i steps (as integers). -/
theorem dyckPath_y_eq_count_diff_int (p : SimpleDigraph.Path dyckDigraph) (i : ℕ)
    (hi : i < p.vertices.length) (hstart : p.start = (0, 0)) :
    ((p.vertices.get ⟨i, hi⟩).2 : ℤ) =
      ((dyckPathToSteps p).take i).count DyckStep.U - ((dyckPathToSteps p).take i).count DyckStep.D := by
  induction i with
  | zero =>
    simp only [List.take_zero, List.count_nil, CharP.cast_eq_zero, sub_zero]
    unfold SimpleDigraph.Path.start at hstart
    have h0 : p.vertices.get ⟨0, hi⟩ = p.vertices.head p.nonempty := by
      rw [List.get_mk_zero hi]
    rw [h0, hstart]
    rfl
  | succ j ih =>
    have hj : j < p.vertices.length := Nat.lt_of_succ_lt hi
    have ihj := ih hj
    have harc := p.arcs_valid j hi
    have hsteps_len : j < (dyckPathToSteps p).length := by
      rw [dyckPathToSteps_length]; omega
    have hstep_j : (dyckPathToSteps p)[j] =
        if (p.vertices.get ⟨j + 1, hi⟩).2 = (p.vertices.get ⟨j, hj⟩).2 + 1
        then DyckStep.U else DyckStep.D := by
      simp only [dyckPathToSteps, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
        List.get_eq_getElem]
    unfold dyckDigraph at harc
    simp only at harc
    rcases harc with ⟨_, hy_up⟩ | ⟨_, hy_down, _⟩
    · have hU : (dyckPathToSteps p)[j] = DyckStep.U := by
        rw [hstep_j]; simp only [hy_up, ↓reduceIte]
      rw [List.take_succ_eq_append_getElem hsteps_len, List.count_append, List.count_append]
      simp only [List.count_singleton, hU]
      have h1 : (if (DyckStep.U == DyckStep.U) = true then 1 else 0) = 1 := by native_decide
      have h2 : (if (DyckStep.U == DyckStep.D) = true then 1 else 0) = 0 := by native_decide
      rw [h1, h2, add_zero, hy_up]; push_cast; omega
    · have heq : (p.vertices.get ⟨j, Nat.lt_of_succ_lt hi⟩).2 = (p.vertices.get ⟨j, hj⟩).2 := rfl
      rw [heq] at hy_down
      have hD : (dyckPathToSteps p)[j] = DyckStep.D := by
        rw [hstep_j]
        have hne : (p.vertices.get ⟨j + 1, hi⟩).2 ≠ (p.vertices.get ⟨j, hj⟩).2 + 1 := by omega
        simp only [hne, ↓reduceIte]
      rw [List.take_succ_eq_append_getElem hsteps_len, List.count_append, List.count_append]
      simp only [List.count_singleton, hD]
      have h1 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
      have h2 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
      rw [h1, h2, add_zero]; push_cast; omega

end LGV
