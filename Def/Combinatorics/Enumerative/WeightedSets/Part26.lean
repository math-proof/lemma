/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.WeightedSets.Part21
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

/-- Main decomposition isomorphism (Lemma \ref{lem.gf.weighted-set.domino.fd}):
    
    Any domino tiling of a height-2 rectangle can be decomposed **uniquely** into a 
    tuple of faultfree tilings of (usually smaller) height-2 rectangles, by cutting 
    it along its faults.
    
    This gives an isomorphism of weighted sets:
      D ≅ F⁰ + F¹ + F² + F³ + ...
    where D = TilingsHeight2 and F = FaultfreeTilingsHeight2.
    
    The isomorphism preserves weights: the sum of the widths of the faultfree tilings
    in the tuple equals the width of the original tiling. -/
def tiling_decomposition_isomorphism :
    WeightedSet.Isomorphism TilingsHeight2 FaultfreeTilingsHeight2.tuples where
  toEquiv := {
    toFun := fun ⟨n, T⟩ => decomposeTiling n T
    invFun := fun ⟨k, ts⟩ => composeTilings k ts
    left_inv := fun ⟨n, T⟩ => composeTilings_decomposeTiling n T
    right_inv := fun ⟨k, ts⟩ => decomposeTiling_composeTilings k ts
  }
  weight_eq := fun ⟨n, T⟩ => by
    simp only [WeightedSet.tuples, TilingsHeight2]
    exact decomposeTiling_weight_sum n T

/-! #### Helper definitions for the Fibonacci recurrence bijection -/


/-- Prepend a vertical domino to a tiling of Rectangle m 2, giving a tiling of Rectangle (m+1) 2.
    
    The new tiling has dominos = {vertical 1 1} ∪ (T.dominos shifted right by 1).
    This is the inverse of restricting at fault 1 when a vertical domino is present. -/
def prependVertical (m : ℕ) (T : Tiling (Rectangle m 2)) : Tiling (Rectangle (m + 1) 2) where
  dominos := {Domino.vertical 1 1} ∪ T.dominos.image (fun d => d.shiftNat 1)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hd1 hd2
    rcases hd1 with rfl | ⟨d1', hd1', rfl⟩ <;> rcases hd2 with rfl | ⟨d2', hd2', rfl⟩
    · exact (hne rfl).elim
    · -- vertical 1 1 vs shifted d2'
      -- vertical 1 1 covers column 1, shifted dominos cover columns ≥ 2
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift]
      rw [Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs vertical 1 1
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift]
      rw [Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs shifted d2'
      have hne' : d1' ≠ d2' := by
        intro heq; subst heq; exact hne rfl
      have hdisj := T.pairwise_disjoint hd1' hd2' hne'
      simp only [Function.onFun, Domino.shiftNat_toShape]
      exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
        simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_image,
               Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with rfl | ⟨d', hd', rfl⟩
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · have hd'_rect := domino_subset_rect m T d' hd'
        rw [Domino.shiftNat_toShape] at hp
        obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
        simp only [Prod.mk.injEq] at heq
        have hxy' := hd'_rect hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hxy'
        omega
    · intro ⟨hx1, hx2, hy1, hy2⟩
      rcases (show x = 1 ∨ x ≥ 2 by omega) with rfl | hx_ge2
      · -- x = 1: covered by vertical 1 1
        use Domino.vertical 1 1, Or.inl rfl
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        have hy12 : y = 1 ∨ y = 2 := by omega
        rcases hy12 with rfl | rfl <;> simp
      · -- x ≥ 2: covered by shifted domino
        have hxy_rect : (x - 1, y) ∈ Rectangle m 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          omega
        rw [← T.cover] at hxy_rect
        simp only [Set.mem_iUnion] at hxy_rect
        obtain ⟨d', hd', hp'⟩ := hxy_rect
        use d'.shiftNat 1, Or.inr ⟨d', hd', rfl⟩
        rw [Domino.shiftNat_toShape]
        refine ⟨(x - 1, y), hp', ?_⟩
        simp only [Prod.mk.injEq]
        constructor <;> first | ring | trivial

/-- Prepend a pair of horizontal dominos to a tiling of Rectangle m 2, giving a tiling of Rectangle (m+2) 2.
    
    The new tiling has dominos = {horizontal 1 1, horizontal 1 2} ∪ (T.dominos shifted right by 2).
    This is the inverse of restricting at fault 2 when horizontal dominos are present. -/
def prependHorizontalPair (m : ℕ) (T : Tiling (Rectangle m 2)) : Tiling (Rectangle (m + 2) 2) where
  dominos := {Domino.horizontal 1 1, Domino.horizontal 1 2} ∪ T.dominos.image (fun d => d.shiftNat 2)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image] at hd1 hd2
    rcases hd1 with (rfl | rfl) | ⟨d1', hd1', rfl⟩ <;> rcases hd2 with (rfl | rfl) | ⟨d2', hd2', rfl⟩
    · exact (hne rfl).elim
    · -- horizontal 1 1 vs horizontal 1 2
      simp only [Function.onFun, Domino.toShape, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1 hx2
      rcases hx1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ <;> rcases hx2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
    · -- horizontal 1 1 vs shifted d2'
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- horizontal 1 2 vs horizontal 1 1
      simp only [Function.onFun, Domino.toShape, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1 hx2
      rcases hx1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ <;> rcases hx2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
    · exact (hne rfl).elim
    · -- horizontal 1 2 vs shifted d2'
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs horizontal 1 1
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs horizontal 1 2
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs shifted d2'
      have hne' : d1' ≠ d2' := by
        intro heq; subst heq; exact hne rfl
      have hdisj := T.pairwise_disjoint hd1' hd2' hne'
      simp only [Function.onFun, Domino.shiftNat_toShape]
      exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
        simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, 
               Set.mem_image, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with (rfl | rfl) | ⟨d', hd', rfl⟩
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · have hd'_rect := domino_subset_rect m T d' hd'
        rw [Domino.shiftNat_toShape] at hp
        obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
        simp only [Prod.mk.injEq] at heq
        have hxy' := hd'_rect hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hxy'
        omega
    · intro ⟨hx1, hx2, hy1, hy2⟩
      have hy12 : y = 1 ∨ y = 2 := by omega
      rcases (show x = 1 ∨ x = 2 ∨ x ≥ 3 by omega) with rfl | rfl | hx_ge3
      · -- x = 1: covered by horizontal 1 y
        rcases hy12 with rfl | rfl
        · use Domino.horizontal 1 1, Or.inl (Or.inl rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
        · use Domino.horizontal 1 2, Or.inl (Or.inr rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
      · -- x = 2: covered by horizontal 1 y
        rcases hy12 with rfl | rfl
        · use Domino.horizontal 1 1, Or.inl (Or.inl rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          right; trivial
        · use Domino.horizontal 1 2, Or.inl (Or.inr rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          right; trivial
      · -- x ≥ 3: covered by shifted domino
        have hxy_rect : (x - 2, y) ∈ Rectangle m 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          omega
        rw [← T.cover] at hxy_rect
        simp only [Set.mem_iUnion] at hxy_rect
        obtain ⟨d', hd', hp'⟩ := hxy_rect
        use d'.shiftNat 2, Or.inr ⟨d', hd', rfl⟩
        rw [Domino.shiftNat_toShape]
        refine ⟨(x - 2, y), hp', ?_⟩
        simp only [Prod.mk.injEq]
        constructor <;> first | ring | trivial

/-! #### Height-3 Rectangle Tilings -/


/-- The set of dominos that fit within a rectangle -/
def DominosInRectangle (n m : ℕ) : Set Domino :=
  {d | d.toShape ⊆ Rectangle n m}

end DominoTilingsZ
end
