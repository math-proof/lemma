/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part6
import Theorem.StatisticalMechanics.Code.Onsager.EdgeUnique


namespace StatMech.Onsager.GeneralInterior

open Finset SimpleGraph Set

open StatMech.Lattice

open StatMech.Euc

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH
  StatMech.Onsager.EdgeUnique StatMech.Onsager.InteriorCells
  StatMech.Onsager.WalkCellRegion StatMech.Onsager.CellCount
  StatMech.Onsager.CellEuler StatMech.Onsager.CellEulerFaithful

variable {n : ℕ} [NeZero n]


theorem exists_odd_cell_at_edge (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (k : Fin n) :
    ∃ c : ℤ × ℤ, rayParity d c.1 c.2 = 1 := by
  set p := pos d k
  have hs := pos_succ d hclosed k
  match hd : d k with
  | 0 =>
      have hpk : pos d (k + 1) = (p.1 + 1, p.2) := by
        rw [hs, hd]
        ext <;> simp [p, stepOf]
      have hmem : k ∈ midSet d p.1 p.2 := by
        simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Or.inl hd, ?_, ?_⟩
        · rw [hpk]
          simp [p]
        · simp [p]
      have hflip : rayParity d p.1 (p.2 - 1) = rayParity d p.1 p.2 + 1 := by
        have h := rayParity_vflip d p.1 (p.2 - 1)
          (by
            rw [show p.2 - 1 + 1 = p.2 by ring]
            exact midSet_card_odd_of_mem d hclosed hsimple hn p.1 p.2 k hmem)
        rwa [show p.2 - 1 + 1 = p.2 by ring] at h
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d p.1 p.2) with h0 | h1
      · refine ⟨(p.1, p.2 - 1), ?_⟩
        simpa [h0] using hflip
      · exact ⟨(p.1, p.2), h1⟩
  | 1 =>
      have hpk : pos d (k + 1) = (p.1, p.2 + 1) := by
        rw [hs, hd]
        ext <;> simp [p, stepOf]
      have hmem : k ∈ straddleSet d (p.1 - 1) p.2 := by
        simp only [straddleSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Or.inl hd, ?_, ?_, ?_⟩
        · simp [p]
        · rw [hpk]
          simp [p]
        · rw [hpk]
          simp [p]
      have hflip : rayParity d (p.1 - 1) p.2 = rayParity d p.1 p.2 + 1 := by
        have h := rayParity_hflip d hclosed (p.1 - 1) p.2
          (straddleSet_card_odd_of_mem d hclosed hsimple hn (p.1 - 1) p.2 k hmem)
        rwa [show p.1 - 1 + 1 = p.1 by ring] at h
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d p.1 p.2) with h0 | h1
      · refine ⟨(p.1 - 1, p.2), ?_⟩
        simpa [h0] using hflip
      · exact ⟨(p.1, p.2), h1⟩
  | 2 =>
      have hpk : pos d (k + 1) = (p.1 - 1, p.2) := by
        rw [hs, hd]
        ext <;> simp [p, stepOf] <;> ring
      have hmem : k ∈ midSet d (p.1 - 1) p.2 := by
        simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Or.inr hd, ?_, ?_⟩
        · rw [hpk]
          simp [p]
        · simp [p]
      have hflip : rayParity d (p.1 - 1) (p.2 - 1) = rayParity d (p.1 - 1) p.2 + 1 := by
        have h := rayParity_vflip d (p.1 - 1) (p.2 - 1)
          (by
            rw [show p.2 - 1 + 1 = p.2 by ring]
            exact midSet_card_odd_of_mem d hclosed hsimple hn (p.1 - 1) p.2 k hmem)
        rwa [show p.2 - 1 + 1 = p.2 by ring] at h
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
          (rayParity d (p.1 - 1) p.2) with h0 | h1
      · refine ⟨(p.1 - 1, p.2 - 1), ?_⟩
        simpa [h0] using hflip
      · exact ⟨(p.1 - 1, p.2), h1⟩
  | 3 =>
      have hpk : pos d (k + 1) = (p.1, p.2 - 1) := by
        rw [hs, hd]
        ext <;> simp [p, stepOf] <;> ring
      have hmem : k ∈ straddleSet d (p.1 - 1) (p.2 - 1) := by
        simp only [straddleSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Or.inr hd, ?_, ?_, ?_⟩
        · simp [p]
        · rw [hpk]
          simp [p]
        · rw [hpk]
          simp [p]
      have hflip : rayParity d (p.1 - 1) (p.2 - 1) = rayParity d p.1 (p.2 - 1) + 1 := by
        have h := rayParity_hflip d hclosed (p.1 - 1) (p.2 - 1)
          (straddleSet_card_odd_of_mem d hclosed hsimple hn (p.1 - 1) (p.2 - 1) k hmem)
        rwa [show p.1 - 1 + 1 = p.1 by ring] at h
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
          (rayParity d p.1 (p.2 - 1)) with h0 | h1
      · refine ⟨(p.1 - 1, p.2 - 1), ?_⟩
        simpa [h0] using hflip
      · exact ⟨(p.1, p.2 - 1), h1⟩


theorem interiorCells_nonempty (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) : (interiorCells d hclosed).Nonempty := by
  obtain ⟨c, hc⟩ := exists_odd_cell_at_edge d hclosed hsimple hn 0
  exact ⟨c, (mem_interiorCells d hclosed c).2 hc⟩

end StatMech.Onsager.GeneralInterior
