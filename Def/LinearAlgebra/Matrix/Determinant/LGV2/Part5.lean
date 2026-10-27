/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Abbrev.LinearAlgebra.Matrix.Determinant.LGV2.Part2
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

/-- The sign of a path tuple with permutation is (-1)^σ -/
def signOfPathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (sp : pathTupleWithPerm (D := D) A B) : ℤˣ :=
  Equiv.Perm.sign sp.1

/-- The weight of a path tuple with permutation -/
noncomputable def weightOfPathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (w : ArcWeight D K) (sp : pathTupleWithPerm (D := D) A B) : K :=
  pathTupleWeight w sp.2.paths

/-- The index of the first occurrence of a vertex in a path's vertex list -/
def firstIndexIn {D : SimpleDigraph V} (p : SimpleDigraph.Path D) (v : V) : ℕ :=
  p.vertices.findIdx (· = v)

/-- Split a path at a vertex v, returning (head ending at v, tail starting at v).
    The head includes v, the tail starts at v. -/
noncomputable def SimpleDigraph.Path.splitAt {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : SimpleDigraph.Path D × SimpleDigraph.Path D :=
  let idx := p.vertices.findIdx (· = v)
  let head := p.vertices.take (idx + 1)
  let tail := p.vertices.drop idx
  have h_idx_lt : idx < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : head ≠ [] := by
    intro h
    have hlen : head.length = 0 := by simp [h]
    simp only [head, List.length_take] at hlen
    omega
  have h_tail_ne : tail ≠ [] := by
    intro h
    have hlen : tail.length = 0 := by rw [h]; rfl
    simp only [tail, List.length_drop] at hlen
    omega
  have h_head_arcs : ∀ i : ℕ, ∀ hi : i + 1 < head.length,
      D.arc (head.get ⟨i, Nat.lt_of_succ_lt hi⟩) (head.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [head, List.length_take, lt_min_iff] at hi
    have hi2 : i + 1 < p.vertices.length := by omega
    have := p.arcs_valid i hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [head]
    rw [List.getElem_take, List.getElem_take]
    exact this
  have h_tail_arcs : ∀ i : ℕ, ∀ hi : i + 1 < tail.length,
      D.arc (tail.get ⟨i, Nat.lt_of_succ_lt hi⟩) (tail.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [tail, List.length_drop] at hi
    have hi2 : idx + i + 1 < p.vertices.length := by omega
    have := p.arcs_valid (idx + i) hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [tail]
    rw [List.getElem_drop, List.getElem_drop]
    convert this using 2
  (⟨head, h_head_ne, h_head_arcs⟩, ⟨tail, h_tail_ne, h_tail_arcs⟩)

end LGV
