/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorSidesFromClusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcedpathconn
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcemono
import Theorem.StatisticalMechanics.Code.Walls.bc2_raydisjoint.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
import Def.StatisticalMechanics.Code.Walls.bc2_core.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc2_corridorCover_of_box {n : ℕ} (h : bc2_BoxForcedCorridorRouting d n) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G :=
  csc_corridorCover_of_distinctClusters
    (fun ω hω => bc2_csc_of_forcedCorridorRouting ω (h ω hω))


theorem bc2_burtonKeane_uniqueness_of_box
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hroute : ∀ n : ℕ, bc2_BoxForcedCorridorRouting d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_corridorCover μ herg hfe bdry hbound hvol hdens
    (fun n => bc2_corridorCover_of_box (hroute n))


theorem bc2_pairwiseSeparated_zero_of_cutDisconnected (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d)
    (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
    (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
    (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ 0 0 0 := by
  
  
  set G : Finset (Sym2 (Site d)) :=
    hrHD_corridorEdges j₁ (0 + 1) ∪ hrHD_corridorEdges j₂ (0 + 1) ∪
      hrHD_corridorEdges j₃ (0 + 1) with hGdef
  have hGmem : ∀ e ∈ G, (0 : Site d) ∈ e := by
    intro e he
    rw [hGdef, Finset.mem_union, Finset.mem_union] at he
    have hcorr : ∀ (j : Fin d), e ∈ hrHD_corridorEdges j (0 + 1) → (0 : Site d) ∈ e := by
      intro j hj
      rw [hrHD_corridorEdges, Finset.mem_image] at hj
      obtain ⟨t, ht, rfl⟩ := hj
      rw [Finset.mem_range] at ht
      have ht0 : t = 0 := by omega
      subst ht0
      rw [Sym2.mem_iff]; left
      simp
    rcases he with (h | h) | h
    · exact hcorr j₁ h
    · exact hcorr j₂ h
    · exact hcorr j₃ h
  have hrm : removeSite (0 : Site d) (forceOpenFinset G ω) = removeSite (0 : Site d) ω :=
    removeSite_forceOpen_eq 0 G hGmem ω
  refine ⟨?_, ?_, ?_⟩
  · change ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) _ _; rw [hrm]; exact hsep12
  · change ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) _ _; rw [hrm]; exact hsep13
  · change ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) _ _; rw [hrm]; exact hsep23


theorem bc2_forcedCorridorRouting_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite)
    (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
    (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
    (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
    bc2_ForcedCorridorRouting ω := by
  have he : ((0 : ℕ) : ℤ) + 1 = (1 : ℤ) := by norm_num
  refine ⟨j₁, j₂, j₃, 0, 0, 0, ⟨hj12, hj13, hj23⟩, ⟨?_, ?_, ?_⟩,
    bc2_pairwiseSeparated_zero_of_cutDisconnected ω j₁ j₂ j₃ hsep12 hsep13 hsep23⟩
  · rw [he]; exact hi1
  · rw [he]; exact hi2
  · rw [he]; exact hi3


theorem bc2_csc_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite)
    (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
    (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
    (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
    csc_DistinctClusterCorridors ω :=
  bc2_csc_of_forcedCorridorRouting ω
    (bc2_forcedCorridorRouting_of_neighbour_witnesses ω hj12 hj13 hj23 hi1 hi2 hi3
      hsep12 hsep13 hsep23)


theorem bc2_core (n : ℕ) :
    (bc2_BoxForcedCorridorRouting d n →
        threeMeetBox d n ⊆
          ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
            CorridorWorks a₁ a₂ a₃ G) ∧
      (∀ {j₁ j₂ j₃ : Fin d} (ω : ConfigSpace (Sym2 (Site d))),
        j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite →
        ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) →
        ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) →
        ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) →
        csc_DistinctClusterCorridors ω) :=
  ⟨fun h => bc2_corridorCover_of_box h,
    fun ω hj12 hj13 hj23 hi1 hi2 hi3 hsep12 hsep13 hsep23 =>
      bc2_csc_neighbour_witnesses ω hj12 hj13 hj23 hi1 hi2 hi3 hsep12 hsep13 hsep23⟩

end Walls
end StatMech
