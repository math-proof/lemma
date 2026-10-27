/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2
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

/-- An arc weight function assigns a ring element to each arc.
    Definition in Theorem thm.lgv.kpaths.wt -/
def ArcWeight (D : SimpleDigraph V) (K : Type*) := (u v : V) → D.arc u v → K

/-- Helper function to compute the product of arc weights along a vertex list.
    Uses recursion on the structure of the list.
    - For an empty list or single vertex, the weight is 1 (no arcs).
    - For a list [v₀, v₁, ...], the weight is w(v₀, v₁) * (weight of [v₁, ...]). -/
noncomputable def pathWeightAux {D : SimpleDigraph V} (w : ArcWeight D K)
    (vertices : List V) (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) : K :=
  match vertices with
  | [] => 1
  | [_] => 1
  | v₀ :: v₁ :: rest =>
    have h : 0 + 1 < (v₀ :: v₁ :: rest).length := by simp
    have arc_proof : D.arc v₀ v₁ := by
      have := arcs_valid 0 h
      simp at this
      exact this
    have rest_arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        D.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      have := arcs_valid (i + 1) hi'
      simp only [List.length_cons, List.get_cons_succ] at this ⊢
      exact this
    w v₀ v₁ arc_proof * pathWeightAux w (v₁ :: rest) rest_arcs_valid

/-- The weight of a path is the product of weights of its arcs.
    w(p) := ∏_{a is an arc of p} w(a) -/
noncomputable def pathWeight {D : SimpleDigraph V} (w : ArcWeight D K) (p : SimpleDigraph.Path D) : K :=
  pathWeightAux w p.vertices p.arcs_valid

/-- The weight of a path tuple is the product of weights of its component paths.
    w(𝐩) := w(p₁) w(p₂) ⋯ w(pₖ) -/
noncomputable def pathTupleWeight {D : SimpleDigraph V} {k : ℕ} (w : ArcWeight D K)
    (ps : Fin k → SimpleDigraph.Path D) : K :=
  ∏ i, pathWeight w (ps i)

end LGV
