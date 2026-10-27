/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.WeightedSets.Part15
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

/-- Restrict a tiling to the left part at a fault position -/
def restrictTilingLeft (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : Tiling (Rectangle k 2) where
  dominos := {d ∈ T.dominos | d.inLeftPart k}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_sep_iff] at hd1 hd2
    exact T.pairwise_disjoint hd1.1 hd2.1 hne
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, ⟨hd, hleft⟩, hp⟩
      have hdomain := T.cover ▸ Set.mem_biUnion hd hp
      simp only [Rectangle, Set.mem_ofPred_eq] at hdomain
      exact ⟨hdomain.1, hleft (x, y) hp, hdomain.2.2.1, hdomain.2.2.2⟩
    · intro ⟨h1, h2, h3, h4⟩
      have hk_lt_n : (k : ℤ) < n := by exact_mod_cast hk.2.1
      have hxy : (x, y) ∈ Rectangle n 2 := by
        simp only [Rectangle, Set.mem_ofPred_eq]
        exact ⟨h1, by omega, h3, h4⟩
      rw [← T.cover] at hxy
      simp only [Set.mem_iUnion] at hxy
      obtain ⟨d, hd, hp⟩ := hxy
      have hlr := domino_left_or_right_at_fault hk d hd
      rcases hlr with hleft | hright
      · exact ⟨d, ⟨hd, hleft⟩, hp⟩
      · -- Contradiction: d is in right part but covers (x, y) with x ≤ k
        exfalso
        have hge := hright (x, y) hp
        omega

/-- Restrict a tiling to the right part at a fault position, shifted to origin -/
def restrictTilingRight (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : Tiling (Rectangle (n - k) 2) where
  dominos := ({d ∈ T.dominos | d.inRightPart k}).image (fun d => d.shiftNeg k)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_image, Set.mem_sep_iff] at hd1 hd2
    obtain ⟨d1', ⟨hd1'_mem, _⟩, rfl⟩ := hd1
    obtain ⟨d2', ⟨hd2'_mem, _⟩, rfl⟩ := hd2
    have hne' : d1' ≠ d2' := by intro heq; subst heq; exact hne rfl
    have hdisj := T.pairwise_disjoint hd1'_mem hd2'_mem hne'
    simp only [Function.onFun, Domino.shiftNeg_toShape]
    exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
      simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
      ext ⟨x, y⟩
      simp only [Set.mem_iUnion, Set.mem_image, Rectangle, Set.mem_ofPred_eq]
      constructor
      · intro ⟨d, hd_img, hp⟩
        obtain ⟨d', ⟨hd', hright⟩, hd_eq⟩ := hd_img
        rw [← hd_eq, Domino.shiftNeg_toShape] at hp
        obtain ⟨p', hp', hp_eq⟩ := hp
        simp only [Prod.mk.injEq] at hp_eq
        have hdomain := T.cover ▸ Set.mem_biUnion hd' hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hdomain
        have hx : p'.1 ≥ k + 1 := hright p' hp'
        have hy : y = p'.2 := hp_eq.2.symm
        constructor
        · omega
        constructor
        · have hk_le_n : (k : ℤ) ≤ n := by exact_mod_cast Nat.le_of_lt hk.2.1
          omega
        constructor
        · rw [hy]; exact hdomain.2.2.1
        · rw [hy]; exact hdomain.2.2.2
      · intro ⟨h1, h2, h3, h4⟩
        have hk_lt_n : (k : ℤ) < n := by exact_mod_cast hk.2.1
        have hxy : ((x + k : ℤ), y) ∈ Rectangle n 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          exact ⟨by omega, by omega, h3, h4⟩
        rw [← T.cover] at hxy
        simp only [Set.mem_iUnion] at hxy
        obtain ⟨d, hd, hp⟩ := hxy
        have hlr := domino_left_or_right_at_fault hk d hd
        rcases hlr with hleft | hright
        · -- Contradiction: d is in left part but covers (x + k, y) with x ≥ 1
          exfalso
          have hle := hleft ((x + k : ℤ), y) hp
          omega
        · refine ⟨d.shiftNeg k, ⟨d, ⟨hd, hright⟩, rfl⟩, ?_⟩
          rw [Domino.shiftNeg_toShape]
          refine ⟨((x + k : ℤ), y), hp, ?_⟩
          simp only [add_sub_cancel_right]

end DominoTilingsZ
end
