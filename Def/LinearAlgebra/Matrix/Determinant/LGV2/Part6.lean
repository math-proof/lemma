/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part4
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

/-- Concatenate two paths where the first path ends at v and the second starts at v.
    The resulting path goes from the start of the first to the end of the second.
    The vertex v appears once in the result (not duplicated). -/
noncomputable def SimpleDigraph.Path.concat {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : SimpleDigraph.Path D :=
  let vertices := p.vertices ++ q.vertices.tail
  have h_ne : vertices ≠ [] := by
    simp only [vertices]
    intro h
    have hlen : (p.vertices ++ q.vertices.tail).length = 0 := by rw [h]; rfl
    simp only [List.length_append, List.length_tail] at hlen
    have hp_ne := p.nonempty
    have hp_len : p.vertices.length ≠ 0 := by
      intro h
      exact hp_ne (List.eq_nil_of_length_eq_zero h)
    omega
  have h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [vertices, List.length_append, List.length_tail] at hi
    simp only [List.get_eq_getElem, vertices]
    by_cases h : i + 1 < p.vertices.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left h]
      exact p.arcs_valid i h
    · push Not at h
      by_cases h' : i < p.vertices.length
      · have hi_eq : i = p.vertices.length - 1 := by omega
        have hq_len : 1 < q.vertices.length := by
          have hq_ne := q.nonempty
          by_contra hq_short
          push Not at hq_short
          have htail_len : q.vertices.tail.length = 0 := by simp only [List.length_tail]; omega
          omega
        rw [List.getElem_append_left h', List.getElem_append_right (by omega)]
        have h1 : p.vertices[i]'h' = p.finish := by 
          simp only [SimpleDigraph.Path.finish, hi_eq, List.getLast_eq_getElem]
        have h_idx : i + 1 - p.vertices.length = 0 := by omega
        have h2 : q.vertices.tail[i + 1 - p.vertices.length]'(by simp; omega) = q.vertices[1]'hq_len := by
          simp only [h_idx, List.getElem_tail]
        rw [h1, h2, hpq]
        have hq_arc := q.arcs_valid 0 hq_len
        simp only [List.get_eq_getElem, SimpleDigraph.Path.start, List.head_eq_getElem] at hq_arc ⊢
        exact hq_arc
      · push Not at h'
        have hi1 : i - p.vertices.length < q.vertices.tail.length := by simp; omega
        have hi2 : i + 1 - p.vertices.length < q.vertices.tail.length := by simp; omega
        rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        have h1 : q.vertices.tail[i - p.vertices.length]'hi1 = 
                  q.vertices[i - p.vertices.length + 1]'(by simp at hi1; omega) := by 
          simp only [List.getElem_tail]
        have h2 : q.vertices.tail[i + 1 - p.vertices.length]'hi2 = 
                  q.vertices[i + 1 - p.vertices.length + 1]'(by simp at hi2; omega) := by 
          simp only [List.getElem_tail]
        rw [h1, h2]
        have hq_arc := q.arcs_valid (i - p.vertices.length + 1) (by simp at hi2; omega)
        simp only [List.get_eq_getElem] at hq_arc
        convert hq_arc using 2; omega
  ⟨vertices, h_ne, h_arcs⟩

end LGV
