import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


private lemma domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this


private lemma partialWidthSum_add_le (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i1 i2 : Fin k) (h : i1 < i2) :
    partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := by
  simp only [partialWidthSum]
  have hi : i1.val < i2.val := h
  have hle : i1.val + 1 ≤ i2.val := hi
  have hk : i1.val + 1 < k := Nat.lt_of_le_of_lt hi i2.isLt
  have hinj : Function.Injective (Fin.castLE hle) := Fin.castLE_injective hle
  have step1 : (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1 = 
               ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := by
    have heq := Fin.sum_univ_castSucc (fun j : Fin (i1.val + 1) => (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1)
    simp only [Fin.last, Fin.val_mk, Fin.val_castSucc] at heq
    linarith [heq]
  calc (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1
      = ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := step1
    _ = ∑ j : Fin (i1.val + 1), (ts ⟨(Fin.castLE hle j).val, Nat.lt_trans (Fin.castLE hle j).isLt i2.isLt⟩).1 := by
          apply Finset.sum_congr rfl; intro x _; simp [Fin.castLE]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (i1.val + 1))).map ⟨Fin.castLE hle, hinj⟩, 
          (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          rw [Finset.sum_map]; simp
    _ ≤ ∑ j : Fin i2.val, (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          apply Finset.sum_le_univ_sum_of_nonneg; intro _; exact Nat.zero_le _


/--
[compose_tilings_has_fault_at_boundary_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (hk : k ≥ 2)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1 := by
-- proof
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


-- created on 2026-10-20
