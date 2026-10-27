/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part21
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

theorem nestedDyckVertices_nonempty (n : ℕ) : nestedDyckVertices n ≠ [] := by
  simp [nestedDyckVertices]

theorem nestedDyckVertices_length (n : ℕ) : (nestedDyckVertices n).length = 4 * n + 1 := by
  simp [nestedDyckVertices]

theorem nestedDyckVertices_getElem (n : ℕ) (i : ℕ) (hi : i < (nestedDyckVertices n).length) :
    (nestedDyckVertices n)[i] = ((i : ℤ) - 2 * n, min i (4 * n - i)) := by
  simp only [nestedDyckVertices, List.getElem_map, List.getElem_finRange]
  rfl

theorem nestedDyckVertices_arcs_valid (n : ℕ) :
    ∀ i : ℕ, ∀ hi : i + 1 < (nestedDyckVertices n).length,
      dyckDigraph.arc ((nestedDyckVertices n).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((nestedDyckVertices n).get ⟨i + 1, hi⟩) := by
  intro i hi
  have hlen : (nestedDyckVertices n).length = 4 * n + 1 := nestedDyckVertices_length n
  rw [hlen] at hi
  simp only [List.get_eq_getElem, nestedDyckVertices_getElem n i (by rw [hlen]; omega),
             nestedDyckVertices_getElem n (i + 1) (by rw [hlen]; exact hi)]
  unfold dyckDigraph
  simp only
  by_cases hcase : i < 2 * n
  · left
    constructor
    · push_cast; ring
    · have h1 : min i (4 * n - i) = i := Nat.min_eq_left (by omega)
      have h2 : min (i + 1) (4 * n - (i + 1)) = i + 1 := Nat.min_eq_left (by omega)
      rw [h1, h2]
  · push Not at hcase
    right
    constructor
    · push_cast; ring
    constructor
    · have h1 : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
      have h2 : min (i + 1) (4 * n - (i + 1)) = 4 * n - i - 1 := Nat.min_eq_right (by omega)
      rw [h1, h2]; omega
    · have h1 : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
      rw [h1]; omega

end LGV
