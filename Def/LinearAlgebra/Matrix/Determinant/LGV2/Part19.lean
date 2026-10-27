/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part17
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

/-- Convert a Dyck path to a DyckWord.
    Each arc (x,y) → (x+1,y+1) becomes U, each arc (x,y) → (x+1,y-1) becomes D.

    **Note:** This definition requires substantial infrastructure to prove well-formedness.
    The key properties are:
    - count_U_eq_count_D: follows from start.2 = 0 = finish.2
    - count_D_le_count_U: follows from y ≥ 0 throughout the path (Dyck condition) -/
def dyckPathToWord (p : SimpleDigraph.Path dyckDigraph) (hstart : p.start = (0, 0))
    (hfinish : p.finish.2 = 0) : DyckWord where
  toList := dyckPathToSteps p
  count_U_eq_count_D := by
    -- The number of U steps equals the number of D steps because we start and end at y = 0
    -- Each U increases y by 1, each D decreases y by 1
    -- So #U - #D = final_y - initial_y = 0 - 0 = 0
    have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil p.nonempty
    have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
    have hfinish_eq : p.finish = p.vertices.get ⟨p.vertices.length - 1, hlast⟩ := by
      unfold SimpleDigraph.Path.finish
      rw [List.getLast_eq_getElem]
      rfl
    have hy := dyckPath_y_eq_count_diff_int p (p.vertices.length - 1) hlast hstart
    have hsteps_len : (dyckPathToSteps p).length = p.vertices.length - 1 := dyckPathToSteps_length p
    have htake : (dyckPathToSteps p).take (p.vertices.length - 1) = dyckPathToSteps p := by
      conv_lhs => rw [← hsteps_len]
      exact List.take_length
    rw [htake] at hy
    rw [hfinish_eq] at hfinish
    have hfinish' : (p.vertices.get ⟨p.vertices.length - 1, hlast⟩).2 = 0 := hfinish
    rw [hfinish'] at hy
    simp only [CharP.cast_eq_zero] at hy
    omega
  count_D_le_count_U := by
    -- At any prefix, #D ≤ #U because y ≥ 0 throughout the path
    -- y = #U - #D, so #D ≤ #U ⟺ y ≥ 0
    intro i
    by_cases hi : i < p.vertices.length
    · have hy := dyckPath_y_eq_count_diff_int p i hi hstart
      -- The y-coordinate is always ≥ 0 (since it's a ℕ)
      -- So count U - count D ≥ 0, i.e., count D ≤ count U
      have hy_nonneg : (0 : ℤ) ≤ (p.vertices.get ⟨i, hi⟩).2 := Int.natCast_nonneg _
      omega
    · -- If i ≥ vertices.length, then take i = full list
      have hsteps_len : (dyckPathToSteps p).length = p.vertices.length - 1 := dyckPathToSteps_length p
      have htake : (dyckPathToSteps p).take i = dyckPathToSteps p := by
        apply List.take_of_length_le
        omega
      rw [htake]
      -- For the full list, count_U = count_D (from above), so count_D ≤ count_U
      have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil p.nonempty
      have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
      have hy := dyckPath_y_eq_count_diff_int p (p.vertices.length - 1) hlast hstart
      have htake' : (dyckPathToSteps p).take (p.vertices.length - 1) = dyckPathToSteps p := by
        conv_lhs => rw [← hsteps_len]
        exact List.take_length
      rw [htake'] at hy
      have hy_nonneg : (0 : ℤ) ≤ (p.vertices.get ⟨p.vertices.length - 1, hlast⟩).2 :=
        Int.natCast_nonneg _
      omega

/-- Helper function to compute the y-coordinate at position i in a DyckWord path -/
def dyckWordY (w : DyckWord) (i : ℕ) : ℕ :=
  (w.toList.take i).count DyckStep.U - (w.toList.take i).count DyckStep.D

/-- Convert a DyckWord to a list of vertices -/
def dyckWordToVertices (w : DyckWord) : List (ℤ × ℕ) :=
  (List.finRange (w.toList.length + 1)).map fun ⟨i, _⟩ => ((i : ℤ), dyckWordY w i)

end LGV
