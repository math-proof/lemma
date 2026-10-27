/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.WeightedSets.Part12
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

/-- The composition function: given a tuple of faultfree tilings, concatenate them
    horizontally to produce a single tiling.
    
    Each faultfree tiling is shifted by the cumulative width of the previous tilings,
    and the union of all shifted dominos forms the composed tiling.
    
    This is the inverse of decomposeTiling. -/
def composeTilings (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    Σ n : ℕ, Tiling (Rectangle n 2) :=
  let totalWidth := ∑ i : Fin k, (ts i).1
  ⟨totalWidth, {
    dominos := composeTilings_dominos k ts
    pairwise_disjoint := by
      intro d1 hd1 d2 hd2 hne
      simp only [composeTilings_dominos, Set.mem_iUnion] at hd1 hd2
      obtain ⟨i1, hi1⟩ := hd1
      obtain ⟨i2, hi2⟩ := hd2
      simp only [composeTilings_component_dominos, Set.mem_image] at hi1 hi2
      obtain ⟨d1', hd1', rfl⟩ := hi1
      obtain ⟨d2', hd2', rfl⟩ := hi2
      -- The shifted dominos are disjoint either because they come from the same component
      -- (and the original dominos are disjoint) or from different components (different x-ranges)
      by_cases heq : i1 = i2
      · -- Same component: use original pairwise disjointness
        subst heq
        have hne' : d1' ≠ d2' := by
          intro h
          subst h
          exact hne rfl
        have hdisj := (ts i1).2.val.pairwise_disjoint hd1' hd2' hne'
        simp only [Function.onFun, Domino.shiftNat_toShape]
        exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
          simp only [Prod.mk.injEq] at h
          ext <;> omega) hdisj
      · -- Different components: disjoint x-ranges
        simp only [Function.onFun]
        exact composeTilings_component_dominos_disjoint k ts i1 i2 heq 
          (d1'.shiftNat (partialWidthSum k ts i1)) 
          (Set.mem_image_of_mem _ hd1')
          (d2'.shiftNat (partialWidthSum k ts i2)) 
          (Set.mem_image_of_mem _ hd2')
    cover := by
        -- The union of shifted dominos covers the rectangle of total width
        -- This follows from each component covering its portion of the rectangle
        ext ⟨x, y⟩
        simp only [Set.mem_iUnion, Rectangle, Set.mem_ofPred_eq]
        constructor
        · -- ⊆ direction: any point in a shifted domino is in the total rectangle
          rintro ⟨d, hd, hp⟩
          simp only [composeTilings_dominos, Set.mem_iUnion] at hd
          obtain ⟨i, hi⟩ := hd
          simp only [composeTilings_component_dominos, Set.mem_image] at hi
          obtain ⟨d', hd', rfl⟩ := hi
          -- Get x-coordinate bounds from shifted_domino_x_in_range'
          have hx := shifted_domino_x_in_range' hd' (partialWidthSum k ts i) (x, y) hp
          -- Get y-coordinate bounds from the original domino
          rw [Domino.shiftNat_toShape] at hp
          obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
          simp only [Prod.mk.injEq] at heq
          have hd'_rect := domino_subset_rect (ts i).1 (ts i).2.val d' hd' hp'
          simp only [Rectangle, Set.mem_ofPred_eq] at hd'_rect
          -- Bound for x: need partialWidthSum + (ts i).1 ≤ totalWidth
          have hbound : partialWidthSum k ts i + (ts i).1 ≤ ∑ j : Fin k, (ts j).1 := by
            simp only [partialWidthSum]
            have hsub : Finset.univ.map (Fin.castLEEmb i.isLt) ⊆ Finset.univ := 
              fun x _ => Finset.mem_univ x
            have h3 := Finset.sum_le_sum_of_subset (f := fun j => (ts j).1) hsub
            have h4 : ∑ j ∈ Finset.univ.map (Fin.castLEEmb i.isLt), (ts j).1 = 
                      ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := by
              rw [Finset.sum_map]
              apply Finset.sum_congr rfl
              intro j _
              rfl
            have h5 : (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1) + (ts i).1 = 
                      ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := by
              rw [Fin.sum_univ_castSucc]
              simp only [Fin.val_castSucc, Fin.val_last]
            calc (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1) + (ts i).1
                = ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := h5
              _ = ∑ j ∈ Finset.univ.map (Fin.castLEEmb i.isLt), (ts j).1 := h4.symm
              _ ≤ ∑ j : Fin k, (ts j).1 := h3
          constructor
          · -- 1 ≤ x
            have : 1 + (partialWidthSum k ts i : ℤ) ≤ x := hx.1
            omega
          constructor
          · -- x ≤ totalWidth
            have : x ≤ (ts i).1 + (partialWidthSum k ts i : ℤ) := hx.2
            have : (partialWidthSum k ts i : ℤ) + (ts i).1 ≤ ∑ j : Fin k, (ts j).1 := by
              exact_mod_cast hbound
            omega
          constructor
          · -- 1 ≤ y
            have hy_eq : y = y' := heq.2.symm
            omega
          · -- y ≤ 2
            have hy_eq : y = y' := heq.2.symm
            omega
        · -- ⊇ direction: any point in the rectangle is covered by some shifted domino
          intro ⟨hx1, hx2, hy1, hy2⟩
          -- Handle k = 0 case: rectangle is empty
          by_cases hk : k = 0
          · -- k = 0 ⇒ totalWidth = 0, so 1 ≤ x ≤ 0 is impossible
            have htw : totalWidth = 0 := by
              simp only [totalWidth]
              subst hk
              rfl
            rw [htw] at hx2
            omega
          · -- k ≥ 1: use point_in_some_component
            have hk' : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
            have hp_rect : (x, y) ∈ Rectangle (∑ i : Fin k, (ts i).1) 2 := by
              simp only [Rectangle, Set.mem_ofPred_eq]
              exact ⟨hx1, hx2, hy1, hy2⟩
            obtain ⟨i, hi_lo, hi_hi⟩ := point_in_some_component k hk' ts (x, y) hp_rect
            -- The unshifted point (x - partialWidthSum, y) is in component i's rectangle
            have hp'_rect : (x - partialWidthSum k ts i, y) ∈ Rectangle (ts i).1 2 := by
              simp only [Rectangle, Set.mem_ofPred_eq]
              constructor
              · omega
              constructor
              · omega
              exact ⟨hy1, hy2⟩
            -- By component's cover property, this point is covered by some domino d'
            rw [← (ts i).2.val.cover] at hp'_rect
            simp only [Set.mem_iUnion] at hp'_rect
            obtain ⟨d', hd', hp'⟩ := hp'_rect
            -- The shifted domino d'.shiftNat (partialWidthSum k ts i) covers (x, y)
            refine ⟨d'.shiftNat (partialWidthSum k ts i), ?_, ?_⟩
            · -- Show the shifted domino is in composeTilings_dominos
              simp only [composeTilings_dominos, composeTilings_component_dominos, 
                         Set.mem_iUnion, Set.mem_image]
              exact ⟨i, d', hd', rfl⟩
            · rw [Domino.shiftNat_toShape]
              refine ⟨(x - partialWidthSum k ts i, y), hp', ?_⟩
              simp only [Prod.mk.injEq]
              constructor
              · omega
              · trivial
    }⟩

end DominoTilingsZ
end
