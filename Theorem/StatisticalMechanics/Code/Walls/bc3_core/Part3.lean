/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_barrierblocks
import Theorem.StatisticalMechanics.Code.Walls.bc3_rhoedgecases
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
import Def.StatisticalMechanics.Code.Walls.bc3_core.Part3
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc3_pairwiseSeparated_of_corridorClustersDisjoint (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ := by
  obtain ⟨h12, h13, h21, h23, _h31, _h32⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · 
    have hq : (hrHD_rayPt j₂ 1 : Site d) ∉ bc3_clusterNbhd ω j₁ (L₁ + 1) := by
      have h := h12 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₂)); simpa using h
    exact bc3_mouth_separated_of_cross ω j₁ j₂ j₃ L₁ L₂ L₃ h12 h13 _ hq
  · 
    have hq : (hrHD_rayPt j₃ 1 : Site d) ∉ bc3_clusterNbhd ω j₁ (L₁ + 1) := by
      have h := h13 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₃)); simpa using h
    exact bc3_mouth_separated_of_cross ω j₁ j₂ j₃ L₁ L₂ L₃ h12 h13 _ hq
  · 
    have hq : (hrHD_rayPt j₃ 1 : Site d) ∉ bc3_clusterNbhd ω j₂ (L₂ + 1) := by
      have h := h23 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₃)); simpa using h
    have hclosed :
        bc3_AdjClosed (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (bc3_clusterNbhd ω j₂ (L₂ + 1)) := by
      rw [bc3_corridorUnion_perm2]
      exact bc3_clusterNbhd_adjClosed_gen ω j₂ j₁ j₃ L₂ L₁ L₃ h21 h23
    exact bc3_barrier_blocks _ (bc3_clusterNbhd ω j₂ (L₂ + 1)) (hrHD_rayPt j₂ 1)
      (hrHD_rayPt j₃ 1) hclosed (bc3_mouth_mem_clusterNbhd (Nat.succ_pos L₂)) hq


theorem bc3_forcedCorridorRouting_of_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} {L₁ L₂ L₃ : ℕ} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    bc2_ForcedCorridorRouting ω :=
  ⟨j₁, j₂, j₃, L₁, L₂, L₃, ⟨hj12, hj13, hj23⟩, ⟨hi1, hi2, hi3⟩,
    bc3_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h⟩


theorem bc3_csc_of_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} {L₁ L₂ L₃ : ℕ} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    csc_DistinctClusterCorridors ω :=
  bc2_csc_of_forcedCorridorRouting ω
    (bc3_forcedCorridorRouting_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 h)


lemma bc3_cluster_bot_singleton (x : Site d) (_hx : x ≠ 0) :
    cluster d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) x = {x} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨self_mem_cluster _ _, ?_⟩
  intro y hy
  rw [mem_cluster] at hy
  
  obtain ⟨w⟩ := hy
  cases w with
  | nil => rfl
  | @cons _ z _ hadj _ =>
      exfalso
      
      have hval : removeSite (0 : Site d) (⊥ : ConfigSpace (Sym2 (Site d))) s(x, z) = true :=
        hadj.2
      by_cases h0 : (0 : Site d) ∈ s(x, z)
      · rw [removeSite_apply_of_mem h0] at hval; exact Bool.false_ne_true hval
      · rw [removeSite_apply_of_notMem h0] at hval; exact Bool.false_ne_true hval


theorem bc3_crossDisjoint_bot {a c : Fin d} (hac : a ≠ c) (R L : ℕ) :
    bc3_CrossDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) a c R L := by
  intro p hp1 _ hmem
  rw [bc3_mem_clusterNbhd] at hmem
  obtain ⟨t, ⟨ht1, _⟩, hin⟩ := hmem
  
  have hat_ne : (hrHD_rayPt a (t : ℤ) : Site d) ≠ 0 := by
    rw [Ne, hrHD_rayPt_eq_zero_iff]; exact_mod_cast (by omega : (t : ℤ) ≠ 0)
  rw [bc3_cluster_bot_singleton _ hat_ne, Set.mem_singleton_iff] at hin
  
  have hcp_ne : (hrHD_rayPt c (p : ℤ) : Site d) ≠ hrHD_rayPt a (t : ℤ) :=
    hrHD_rayPt_disjoint_of_ne (Ne.symm hac) (by exact_mod_cast (by omega : (p : ℤ) ≠ 0))
  exact hcp_ne hin


theorem bc3_corridorClustersDisjoint_bot {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) (L₁ L₂ L₃ : ℕ) :
    bc3_CorridorClustersDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ :=
  ⟨bc3_crossDisjoint_bot hj12 _ _, bc3_crossDisjoint_bot hj13 _ _,
    bc3_crossDisjoint_bot (Ne.symm hj12) _ _, bc3_crossDisjoint_bot hj23 _ _,
    bc3_crossDisjoint_bot (Ne.symm hj13) _ _, bc3_crossDisjoint_bot (Ne.symm hj23) _ _⟩


theorem bc3_pairwiseSeparated_bot {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) (L₁ L₂ L₃ : ℕ) :
    bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ :=
  bc3_pairwiseSeparated_of_corridorClustersDisjoint _ j₁ j₂ j₃ L₁ L₂ L₃
    (bc3_corridorClustersDisjoint_bot hj12 hj13 hj23 L₁ L₂ L₃)

end Walls
end StatMech
