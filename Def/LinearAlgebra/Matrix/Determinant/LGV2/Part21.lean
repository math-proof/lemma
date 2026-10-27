/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part19
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

/-- Create translated path by shifting x-coordinates -/
def translatePath (d : ℤ) (p : SimpleDigraph.Path dyckDigraph) :
    SimpleDigraph.Path dyckDigraph where
  vertices := p.vertices.map (translateVertex d)
  nonempty := by simp [p.nonempty]
  arcs_valid := by
    intro k hk
    simp only [List.length_map] at hk
    have hk' : k < p.vertices.length := Nat.lt_of_succ_lt hk
    have hk'' : k + 1 < p.vertices.length := hk
    -- Need to show arc at position k in the mapped list
    -- vertices.get ⟨k, _⟩ = (vertices.map f).get ⟨k, _⟩ = f (vertices.get ⟨k, _⟩)
    have h1 : (p.vertices.map (translateVertex d)).get ⟨k, by simp; exact hk'⟩ = 
              translateVertex d (p.vertices.get ⟨k, hk'⟩) := by
      simp [List.get_eq_getElem]
    have h2 : (p.vertices.map (translateVertex d)).get ⟨k + 1, by simp; exact hk''⟩ = 
              translateVertex d (p.vertices.get ⟨k + 1, hk''⟩) := by
      simp [List.get_eq_getElem]
    rw [h1, h2]
    rw [← dyckDigraph_arc_translate d]
    exact p.arcs_valid k hk

/-!
### Nested Dyck Paths for the Catalan Hankel Determinant

The nested Dyck path from (-2n, 0) to (2n, 0) goes:
(-2n, 0) → (-2n+1, 1) → ... → (0, 2n) → (1, 2n-1) → ... → (2n, 0)

At step i (0 ≤ i ≤ 4n), the vertex is (i - 2n, min(i, 4n - i)).
-/


/-- The vertices of the nested Dyck path from (-2n, 0) to (2n, 0) -/
def nestedDyckVertices (n : ℕ) : List (ℤ × ℕ) :=
  (List.finRange (4 * n + 1)).map fun ⟨i, _⟩ =>
    ((i : ℤ) - 2 * n, min i (4 * n - i))

end LGV
