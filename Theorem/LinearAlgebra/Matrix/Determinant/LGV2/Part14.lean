/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part15
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

theorem pathVerticesList_length (a : ℕ) (S : Finset (Fin a)) :
    (pathVerticesList a S).length = a + 1 := by simp [pathVerticesList]

theorem pathVerticesList_nonempty (a : ℕ) (S : Finset (Fin a)) :
    pathVerticesList a S ≠ [] := by simp [pathVerticesList]

theorem pathVerticesList_getElem (a : ℕ) (S : Finset (Fin a)) (i : ℕ) (hi : i < a + 1) :
    (pathVerticesList a S)[i]'(by rw [pathVerticesList_length]; exact hi) = vertexAtPos a S i := by
  simp only [pathVerticesList, List.getElem_ofFn]

/-- Consecutive vertices in the path satisfy the arc relation -/
theorem vertexAtPos_arc (a : ℕ) (S : Finset (Fin a)) (i : Fin a) :
    integerLattice.arc (vertexAtPos a S i.val) (vertexAtPos a S (i.val + 1)) := by
  simp only [vertexAtPos, eastStepCount, integerLattice]
  by_cases hi : i ∈ S
  · -- i ∈ S: east step (x increases by 1, y stays the same)
    left
    have hfilter : (S.filter (fun j => j.val < i.val + 1)).card = 
                   (S.filter (fun j => j.val < i.val)).card + 1 := by
      have heq : S.filter (fun j => j.val < i.val + 1) = 
                 insert i (S.filter (fun j => j.val < i.val)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · intro ⟨hj, hlt⟩
          by_cases hji : j = i
          · left; exact hji
          · right; exact ⟨hj, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) (fun h => hji (Fin.ext h))⟩
        · intro h; rcases h with rfl | ⟨hj, hlt⟩
          · exact ⟨hi, Nat.lt_succ_self _⟩
          · exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
      rw [heq]
      have hnotmem : i ∉ S.filter (fun j => j.val < i.val) := by
        simp only [Finset.mem_filter, not_and, not_lt]; intro _; exact le_refl _
      rw [Finset.card_insert_eq_ite, if_neg hnotmem]
    constructor
    · simp only [hfilter]; push_cast; ring
    · simp only [hfilter]; push_cast; ring
  · -- i ∉ S: north step (x stays the same, y increases by 1)
    right
    have hfilter : (S.filter (fun j => j.val < i.val + 1)).card = 
                   (S.filter (fun j => j.val < i.val)).card := by
      congr 1; ext j; simp only [Finset.mem_filter]
      constructor
      · intro ⟨hj, hlt⟩
        constructor
        · exact hj
        · by_cases hji : j.val = i.val
          · exfalso; have : j = i := Fin.ext hji; rw [this] at hj; exact hi hj
          · exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hji
      · intro ⟨hj, hlt⟩; exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
    constructor
    · simp only [hfilter]
    · simp only [hfilter]; push_cast; ring

end LGV
