/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.Combinatorics.Enumerative.WeightedSets
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

/-- A faultfree tiling has no faults, so faultPositions is empty -/
theorem faultPositions_empty_of_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hff : isFaultfree n T) : faultPositions n T = ∅ := by
  ext k
  simp only [faultPositions, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact hff.2 k

/-- A faultfree tiling has non-nonempty faultPositions -/
theorem faultPositions_not_nonempty_of_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hff : isFaultfree n T) : ¬(faultPositions n T).Nonempty := by
  rw [faultPositions_empty_of_isFaultfree n T hff]
  exact Set.not_nonempty_empty

/-! ##### Helper lemmas for k >= 2 case of decomposeTiling_composeTilings -/

/-- For k >= 2, the composed tiling has a fault at position (ts 0).1 -/
theorem composeTilings_hasFault_at_boundary (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1 := by
  -- Need to show: (ts 0).1 > 0, (ts 0).1 < total width, and no horizontal domino crosses position (ts 0).1
  set w0 := (ts ⟨0, by omega⟩).1 with hw0_def
  have hpos : w0 > 0 := (ts ⟨0, by omega⟩).2.property.1
  -- Total width is sum of all component widths
  have htotal : (composeTilings k ts).1 = ∑ i : Fin k, (ts i).1 := rfl
  -- Since k >= 2, there's at least one more component with positive width
  have hlt : w0 < (composeTilings k ts).1 := by
    rw [htotal]
    have h1 : (ts ⟨1, by omega⟩).1 > 0 := (ts ⟨1, by omega⟩).2.property.1
    have hdiff : (⟨0, by omega⟩ : Fin k) ≠ (⟨1, by omega⟩ : Fin k) := by simp
    have hsum : w0 + (ts ⟨1, by omega⟩).1 ≤ ∑ i : Fin k, (ts i).1 := by
      have := Finset.sum_pair hdiff (f := fun i => (ts i).1)
      calc w0 + (ts ⟨1, by omega⟩).1 
          = ∑ i ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin k)), (ts i).1 := by rw [this]
        _ ≤ ∑ i : Fin k, (ts i).1 := by
          apply Finset.sum_le_sum_of_subset
          intro i _
          exact Finset.mem_univ i
    omega
  constructor
  · exact hpos
  constructor
  · exact hlt
  · -- Show no horizontal domino crosses position w0
    intro d hd
    simp only [composeTilings, composeTilings_dominos, Set.mem_iUnion] at hd
    obtain ⟨j, hj⟩ := hd
    simp only [composeTilings_component_dominos, Set.mem_image] at hj
    obtain ⟨d', hd', rfl⟩ := hj
    -- d' is a domino from component j, shifted by partialWidthSum k ts j
    cases d' with
    | horizontal i jj =>
      -- Horizontal domino at position i in component j
      -- After shifting, position is i + partialWidthSum k ts j
      simp only [Domino.shiftNat, Domino.shift]
      -- Case split on j
      by_cases hj0 : j.val = 0
      · -- j = 0: domino from first component
        left
        have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
        have hpws : partialWidthSum k ts j = 0 := by
          rw [hj_eq]
          exact partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
        simp only [hpws, Nat.cast_zero, add_zero]
        -- d' = horizontal i jj is in (ts j).2.val.dominos
        -- Since ts j is faultfree with width (ts j).1, we have i < (ts j).1
        have hd'_in : Domino.horizontal i jj ∈ (ts j).2.val.dominos := hd'
        have hsub := domino_subset_rect (ts j).1 (ts j).2.val (Domino.horizontal i jj) hd'_in
        -- The domino's rightmost point (i+1, jj) is in Rectangle (ts j).1 2
        have hright : (i + 1, jj) ∈ (Domino.horizontal i jj).toShape := by simp [Domino.toShape]
        have hright_rect := hsub hright
        simp only [Rectangle, Set.mem_ofPred_eq] at hright_rect
        -- hright_rect : 1 ≤ i + 1 ∧ i + 1 ≤ (ts j).1 ∧ 1 ≤ jj ∧ jj ≤ 2
        -- We need i < w0, i.e., i < (ts ⟨0, _⟩).1
        -- Since j = ⟨0, _⟩, we have (ts j).1 = w0
        have hw0_eq : (ts j).1 = w0 := by rw [hj_eq]
        have hi_bound : i + 1 ≤ w0 := by rw [← hw0_eq]; exact hright_rect.2.1
        linarith
      · -- j >= 1: domino from later component
        right
        have hj_pos : j.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hj0
        have hj1 : (⟨0, by omega⟩ : Fin k) < j := by simp [Fin.lt_def]; omega
        have hpws_ge : partialWidthSum k ts j ≥ w0 := by
          have := partialWidthSum_add_le k ts ⟨0, by omega⟩ j hj1
          simp only [hw0_def] at this ⊢
          omega
        -- The shifted position is i + partialWidthSum k ts j >= 1 + w0 = w0 + 1
        have hi_pos : i ≥ 1 := by
          have hd'_in : Domino.horizontal i jj ∈ (ts j).2.val.dominos := hd'
          have hsub := domino_subset_rect (ts j).1 (ts j).2.val (Domino.horizontal i jj) hd'_in
          have hleft : (i, jj) ∈ (Domino.horizontal i jj).toShape := by simp [Domino.toShape]
          have hleft_rect := hsub hleft
          simp only [Rectangle, Set.mem_ofPred_eq] at hleft_rect
          omega
        calc (i : ℤ) + (partialWidthSum k ts j : ℤ) 
            ≥ 1 + (w0 : ℤ) := by omega
          _ = (w0 : ℤ) + 1 := by ring
    | vertical i jj =>
      -- Vertical dominos don't affect faults
      trivial

/-- For k >= 1, there are no faults at positions less than (ts 0).1 in the composed tiling -/
theorem composeTilings_no_fault_before_boundary (k : ℕ) (hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (p : ℕ) (hp : p < (ts ⟨0, hk⟩).1) : ¬hasFault (composeTilings k ts).1 (composeTilings k ts).2 p := by
  intro hfault
  -- If there's a fault at p < (ts 0).1, then the first component would have a fault at p
  -- But the first component is faultfree, contradiction
  have hff := (ts ⟨0, hk⟩).2.property
  have hno_fault := hff.2 p
  apply hno_fault
  -- Show hasFault (ts 0).1 (ts 0).2.val p
  have hpos : p > 0 := hfault.1
  have hlt : p < (ts ⟨0, hk⟩).1 := hp
  constructor
  · exact hpos
  constructor
  · exact hlt
  · -- Show no horizontal domino in (ts 0).2.val crosses position p
    intro d hd
    -- d is in (ts 0).2.val.dominos
    -- The shifted version d.shiftNat 0 = d is in composeTilings_dominos
    have hd_shifted : d.shiftNat (partialWidthSum k ts ⟨0, hk⟩) ∈ (composeTilings k ts).2.dominos := by
      simp only [composeTilings, composeTilings_dominos, Set.mem_iUnion]
      refine ⟨⟨0, hk⟩, ?_⟩
      simp only [composeTilings_component_dominos, Set.mem_image]
      exact ⟨d, hd, rfl⟩
    have hpws0 : partialWidthSum k ts ⟨0, hk⟩ = 0 := partialWidthSum_zero k ts ⟨0, hk⟩ rfl
    simp only [hpws0, Domino.shiftNat_zero] at hd_shifted
    -- Use the fault condition at p in the composed tiling
    have hcross := hfault.2.2 d hd_shifted
    exact hcross

/-- The minimum fault in a composed tiling with k >= 2 components is at (ts 0).1 -/
theorem composeTilings_minFault_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hne : (faultPositions (composeTilings k ts).1 (composeTilings k ts).2).Nonempty) :
    minFault (composeTilings k ts).1 (composeTilings k ts).2 hne = (ts ⟨0, by omega⟩).1 := by
  -- The minimum fault is (ts 0).1 because:
  -- 1. There's a fault at (ts 0).1 (by composeTilings_hasFault_at_boundary)
  -- 2. There are no faults at positions < (ts 0).1 (by composeTilings_no_fault_before_boundary)
  have hfault := composeTilings_hasFault_at_boundary k hk ts
  have hmin := minFault_hasFault (composeTilings k ts).1 (composeTilings k ts).2 hne
  have hle := minFault_le (composeTilings k ts).1 (composeTilings k ts).2 hne (ts ⟨0, by omega⟩).1 hfault
  -- Show minFault >= (ts 0).1 by contradiction
  by_contra hne'
  push Not at hne'
  have hlt : minFault (composeTilings k ts).1 (composeTilings k ts).2 hne < (ts ⟨0, by omega⟩).1 := by
    omega
  have hno := composeTilings_no_fault_before_boundary k (by omega : k ≥ 1) ts 
    (minFault (composeTilings k ts).1 (composeTilings k ts).2 hne) hlt
  exact hno hmin

end DominoTilingsZ
end
