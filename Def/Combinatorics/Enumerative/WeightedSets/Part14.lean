/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.WeightedSets.Part8
open PowerSeries Finset BigOperators

/-!
# The Generating Function of a Weighted Set

This file formalizes the theory of weighted sets and their weight generating functions,
following Section sec.gf.weighted-set of the Algebraic Combinatorics notes.

A weighted set is a set equipped with a weight function to ℕ. When the set is "finite-type"
(only finitely many elements of each weight), we can define its weight generating function
as a formal power series.

## Main Definitions

* `WeightedSet`: A set with a weight function to ℕ
* `WeightedSet.IsFiniteType`: Predicate for finite-type weighted sets
* `WeightedSet.weightGenFun`: The weight generating function of a finite-type weighted set
* `WeightedSet.Isomorphism`: Weight-preserving bijections between weighted sets
* `WeightedSet.disjointUnion`: Disjoint union of weighted sets (A + B)
* `WeightedSet.prod`: Product of weighted sets (A × B) with additive weights
* `WeightedSet.pow`: Cartesian power of a weighted set
* `WeightedSet.tuples`: Infinite disjoint union W^0 + W^1 + W^2 + ... (Kleene star)

## Main Results

* `WeightedSet.weightGenFun_eq_of_isomorphic`: Isomorphic weighted sets have equal generating functions
* `WeightedSet.weightGenFun_disjointUnion`: ḡ(A + B) = ḡ(A) + ḡ(B)
* `WeightedSet.weightGenFun_prod`: ḡ(A × B) = ḡ(A) · ḡ(B)
* `WeightedSet.weightGenFun_pow`: ḡ(A^k) = ḡ(A)^k
* `DominoTilingsZ.tiling_decomposition_isomorphism`: D ≅ F^0 + F^1 + F^2 + ... (Lemma lem.gf.weighted-set.domino.fd)

## Applications

The file includes applications to:
* Counting compositions (recovering the formula for the generating function of compositions)
* Domino tilings of height-2 rectangles (connection to Fibonacci numbers)

Note: Height-3 domino tilings are handled in `Details/DominoTilings.lean`.

## References

* [Flajolet and Sedgewick, *Analytic Combinatorics*, Part A][FlaSed09]
* [Fink, *Enumerative Combinatorics*, §3.3-§3.4][Fink17]

## Tags

weighted set, generating function, combinatorial class, domino tiling
-/


noncomputable section

variable {R : Type*} [CommSemiring R]

namespace DominoTilingsZ

/-- Shift a tiling to a new position -/
def Tiling.shift {n m : ℕ} (T : Tiling (Rectangle n m)) (offset : ℤ) :
    Tiling {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} where
  dominos := shiftDominos T.dominos offset
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [shiftDominos, Set.mem_image] at hd1 hd2
    obtain ⟨d1', hd1', rfl⟩ := hd1
    obtain ⟨d2', hd2', rfl⟩ := hd2
    have hne' : d1' ≠ d2' := by
      intro heq; subst heq; exact hne rfl
    have hdisj := T.pairwise_disjoint hd1' hd2' hne'
    simp only [Function.onFun, Domino.shift_toShape]
    exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
      simp only [Prod.mk.injEq] at h
      ext <;> omega) hdisj
  cover := by
    have hcover := T.cover
    have heq : (Rectangle n m).image (fun p => (p.1 + offset, p.2)) = 
        {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} := 
      Rectangle_shift n m offset
    rw [← heq]
    ext p
    simp only [Set.mem_iUnion, Set.mem_image, shiftDominos, exists_prop]
    constructor
    · rintro ⟨d, ⟨d', hd', rfl⟩, hp⟩
      rw [Domino.shift_toShape] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      have hp'_rect : p' ∈ Rectangle n m := by
        rw [← hcover]
        exact Set.mem_biUnion hd' hp'
      exact ⟨p', hp'_rect, rfl⟩
    · rintro ⟨p', hp', rfl⟩
      rw [← hcover] at hp'
      simp only [Set.mem_iUnion, exists_prop] at hp'
      obtain ⟨d', hd', hp''⟩ := hp'
      refine ⟨d'.shift offset, ⟨d', hd', rfl⟩, ?_⟩
      rw [Domino.shift_toShape]
      exact ⟨p', hp'', rfl⟩

/-- The tiling of the empty rectangle (width 0) -/
def emptyTiling2 : Tiling (Rectangle 0 2) := by
  rw [Rectangle_zero_left]
  exact Tiling.empty

/-- Cast a tiling along rectangle equality -/
def Tiling.cast {S S' : Shape} (h : S = S') (T : Tiling S) : Tiling S' where
  dominos := T.dominos
  pairwise_disjoint := T.pairwise_disjoint
  cover := by rw [← h]; exact T.cover

end DominoTilingsZ
end
