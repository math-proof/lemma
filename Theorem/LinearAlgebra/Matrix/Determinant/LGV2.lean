/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2
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

/-- Each arc in the integer lattice increases coordinates (or keeps them equal) -/
theorem integerLattice_arc_nondecreasing (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    u.1 ≤ v.1 ∧ u.2 ≤ v.2 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Each arc in the integer lattice increases the sum x + y by exactly 1 -/
theorem integerLattice_arc_sum (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    v.1 + v.2 = u.1 + u.2 + 1 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Coordinates are monotone along a path in the integer lattice -/
theorem integerLattice_path_monotone (p : SimpleDigraph.Path integerLattice) (i j : ℕ)
    (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j) :
    (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 ∧
    (p.vertices.get ⟨i, hi⟩).2 ≤ (p.vertices.get ⟨j, hj⟩).2 := by
  induction j with
  | zero =>
    simp only [Nat.le_zero] at hij
    subst hij
    constructor <;> rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · constructor <;> rfl
    · have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
      have hik' : i ≤ k := Nat.lt_succ_iff.mp hik
      obtain ⟨h1, h2⟩ := ih hk hik'
      have harc : integerLattice.arc (p.vertices.get ⟨k, hk⟩) (p.vertices.get ⟨k + 1, hj⟩) :=
        p.arcs_valid k hj
      obtain ⟨h3, h4⟩ := integerLattice_arc_nondecreasing _ _ harc
      exact ⟨le_trans h1 h3, le_trans h2 h4⟩

/-- Start coordinates ≤ finish coordinates for any path in the integer lattice -/
theorem integerLattice_path_start_le_finish (p : SimpleDigraph.Path integerLattice) :
    p.start.1 ≤ p.finish.1 ∧ p.start.2 ≤ p.finish.2 := by
  have hne := p.nonempty
  have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have h := integerLattice_path_monotone p 0 (p.vertices.length - 1) hlen hlast (Nat.zero_le _)
  simp only [SimpleDigraph.Path.start, SimpleDigraph.Path.finish]
  convert h using 2 <;> simp [List.head_eq_getElem, List.getLast_eq_getElem]

/-- Helper for path_sum_eq: proves the sum formula by induction on the list -/
theorem integerLattice_path_sum_eq_aux (l : List (ℤ × ℤ)) (hne : l ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < l.length, integerLattice.arc (l.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (l.get ⟨i + 1, hi⟩)) :
    (l.getLast hne).1 + (l.getLast hne).2 = (l.head hne).1 + (l.head hne).2 + (l.length - 1) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hne' : y :: ys ≠ [] := List.cons_ne_nil y ys
      have harcs' : ∀ i : ℕ, ∀ hi : i + 1 < (y :: ys).length,
          integerLattice.arc ((y :: ys).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((y :: ys).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (x :: y :: ys).length := by simp at hi ⊢; omega
        have := harcs (i + 1) hi'
        simp only [List.length_cons, List.get_cons_succ] at this ⊢
        exact this
      have harc_xy : integerLattice.arc x y := by
        have := harcs 0 (by simp : 0 + 1 < (x :: y :: ys).length)
        simp at this
        exact this
      have hsum_xy := integerLattice_arc_sum x y harc_xy
      specialize ih hne' harcs'
      simp only [List.getLast_cons hne', List.head_cons, List.length_cons] at ih ⊢
      omega

/-- The sum of coordinates increases by exactly (length - 1) along a path -/
theorem integerLattice_path_sum_eq (p : SimpleDigraph.Path integerLattice) :
    p.finish.1 + p.finish.2 = p.start.1 + p.start.2 + (p.vertices.length - 1) :=
  integerLattice_path_sum_eq_aux p.vertices p.nonempty p.arcs_valid

/-- Path length is determined by start and finish coordinates -/
theorem integerLattice_path_length_eq (p : SimpleDigraph.Path integerLattice) :
    (p.vertices.length : ℤ) = p.finish.1 + p.finish.2 - p.start.1 - p.start.2 + 1 := by
  have h := integerLattice_path_sum_eq p
  have hpos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  omega

/-- Sum at vertex i equals start sum + i -/
theorem integerLattice_path_vertex_sum (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i < p.vertices.length) :
    (p.vertices.get ⟨i, hi⟩).1 + (p.vertices.get ⟨i, hi⟩).2 = p.start.1 + p.start.2 + i := by
  induction i with
  | zero =>
    simp only [SimpleDigraph.Path.start, CharP.cast_eq_zero, add_zero]
    have : p.vertices.get ⟨0, hi⟩ = p.vertices.head p.nonempty := by
      simp [List.head_eq_getElem, List.get_eq_getElem]
    rw [this]
  | succ k ih =>
    have hk : k < p.vertices.length := Nat.lt_of_succ_lt hi
    have ihk := ih hk
    have harc := p.arcs_valid k hi
    have hsum := integerLattice_arc_sum _ _ harc
    omega

/-- Vertices of a lattice path are bounded by start and finish coordinates -/
theorem integerLattice_path_vertices_bounded (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i < p.vertices.length) :
    p.start.1 ≤ (p.vertices.get ⟨i, hi⟩).1 ∧ (p.vertices.get ⟨i, hi⟩).1 ≤ p.finish.1 ∧
    p.start.2 ≤ (p.vertices.get ⟨i, hi⟩).2 ∧ (p.vertices.get ⟨i, hi⟩).2 ≤ p.finish.2 := by
  have hne := p.nonempty
  have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have h1 := integerLattice_path_monotone p 0 i hlen hi (Nat.zero_le _)
  have h2 := integerLattice_path_monotone p i (p.vertices.length - 1) hi hlast (Nat.le_sub_one_of_lt hi)
  simp only [SimpleDigraph.Path.start, SimpleDigraph.Path.finish]
  constructor
  · convert h1.1 using 1; simp [List.head_eq_getElem]
  constructor
  · convert h2.1 using 1; simp [List.getLast_eq_getElem]
  constructor
  · convert h1.2 using 1; simp [List.head_eq_getElem]
  · convert h2.2 using 1; simp [List.getLast_eq_getElem]

/-- Paths in the integer lattice are determined by their vertex list -/
theorem integerLattice_path_ext (p q : SimpleDigraph.Path integerLattice)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq] at h ⊢
  exact h

/-- The integer lattice is path-finite -/
theorem integerLattice_pathFinite : integerLattice.IsPathFinite := by
  intro u v
  by_cases h : v.1 < u.1 ∨ v.2 < u.2
  · -- Case 1: No paths exist (would need to go backwards)
    convert Set.finite_empty
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hstart hfinish
    have hle := integerLattice_path_start_le_finish p
    rw [hstart, hfinish] at hle
    omega
  · -- Case 2: Paths exist but are finite
    push Not at h
    -- Define the path length and bounding box
    let n := (v.1 - u.1 + v.2 - u.2 + 1).toNat
    let box : Finset (ℤ × ℤ) := (Finset.Icc u.1 v.1) ×ˢ (Finset.Icc u.2 v.2)
    -- Define the subtype of paths from u to v
    let S := {p : SimpleDigraph.Path integerLattice | p.start = u ∧ p.finish = v}
    -- Show S is finite by injecting into Fin n → box
    suffices Finite S by exact Set.finite_coe_iff.mpr this
    -- Define the injection: map each path to its vertex list as a function
    let f : S → (Fin n → box) := fun ⟨p, hp⟩ i =>
      let hi : i.val < p.vertices.length := by
        have hlen := integerLattice_path_length_eq p
        rw [hp.1, hp.2] at hlen
        simp only [n] at hlen ⊢
        have := i.isLt
        omega
      ⟨p.vertices.get ⟨i.val, hi⟩, by
        have hbd := integerLattice_path_vertices_bounded p i.val hi
        rw [hp.1, hp.2] at hbd
        simp only [box, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hbd.1, hbd.2.1⟩, ⟨hbd.2.2.1, hbd.2.2.2⟩⟩⟩
    have hinj : Function.Injective f := by
      intro ⟨p, hp⟩ ⟨q, hq⟩ heq
      simp only [Subtype.mk.injEq, f] at heq ⊢
      apply integerLattice_path_ext
      apply List.ext_get
      · -- Lengths are equal (both determined by u and v)
        have hlenp := integerLattice_path_length_eq p
        have hlenq := integerLattice_path_length_eq q
        rw [hp.1, hp.2] at hlenp
        rw [hq.1, hq.2] at hlenq
        omega
      · -- Elements are equal at each position
        intro i hip hiq
        have heqi := congr_fun heq ⟨i, by
          have hlenp := integerLattice_path_length_eq p
          rw [hp.1, hp.2] at hlenp
          simp only [n]
          omega⟩
        simp only [Subtype.mk.injEq] at heqi
        exact heqi
    exact Finite.of_injective f hinj

end LGV
