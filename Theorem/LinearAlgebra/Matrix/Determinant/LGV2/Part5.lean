/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part6
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

omit [DecidableEq V] in
/-- The concatenation of two paths starts at the first path's start -/
theorem SimpleDigraph.Path.concat_start {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).start = p.start := by
  unfold concat start
  simp only
  exact List.head_append_of_ne_nil (l' := q.vertices.tail) p.nonempty

omit [DecidableEq V] in
/-- The concatenation of two paths ends at the second path's finish -/
theorem SimpleDigraph.Path.concat_finish {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).finish = q.finish := by
  unfold concat finish
  simp only
  have hq_ne := q.nonempty
  by_cases h : q.vertices.tail = []
  · have hq_len : q.vertices.length = 1 := by
      have : q.vertices.tail.length = 0 := by simp [h]
      simp only [List.length_tail] at this
      have hq_pos : 0 < q.vertices.length := List.length_pos_of_ne_nil hq_ne
      omega
    have hq_finish_eq_start : q.vertices.getLast hq_ne = q.vertices.head hq_ne := by
      rw [List.getLast_eq_getElem, List.head_eq_getElem]; congr; omega
    simp only [h, List.append_nil]
    rw [hq_finish_eq_start]
    unfold start at hpq
    rw [← hpq]; unfold finish; rfl
  · rw [List.getLast_append_of_ne_nil _ h, List.getLast_tail h]

/-- The head of splitAt starts at the original path's start -/
theorem SimpleDigraph.Path.splitAt_head_start {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).1.start = p.start := by
  unfold splitAt start
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : p.vertices.take (p.vertices.findIdx (· = v) + 1) ≠ [] := by
    intro h; have hlen : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 0 := by simp [h]
    simp only [List.length_take] at hlen; omega
  exact List.head_take h_head_ne

/-- The tail of splitAt ends at the original path's finish -/
theorem SimpleDigraph.Path.splitAt_tail_finish {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).2.finish = p.finish := by
  unfold splitAt finish
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_drop_ne : p.vertices.drop (p.vertices.findIdx (· = v)) ≠ [] := by
    intro h; have hlen : (p.vertices.drop (p.vertices.findIdx (· = v))).length = 0 := by rw [h]; rfl
    simp only [List.length_drop] at hlen; omega
  rw [List.getLast_drop h_drop_ne]

end LGV
