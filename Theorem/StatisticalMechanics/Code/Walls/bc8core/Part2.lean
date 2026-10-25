/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc8distinctcutclusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc8nocrossing.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc8cutleavesinfinite
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Def.StatisticalMechanics.Code.Walls.bc8core
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc8_canonicalTrif_of_originRewiring (n : ℕ) (hrw : bc8_OriginRewiring d n)
    (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n) :
    ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 := by
  obtain ⟨W, hW0, a₁, a₂, a₃, hadj1, hadj2, hadj3, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ := hrw ω hω
  exact ⟨W, hW0, bc8_isCanonicalTrifurcation_of_threeArms (forceOpenFinset W ω)
    hadj1 hadj2 hadj3 hi1 hi2 hi3 hcd12 hcd13 hcd23⟩


theorem bc8_corridorWorks_of_rewiringData (ω : ConfigSpace (Sym2 (Site d)))
    {W : Finset (Sym2 (Site d))} {a₁ a₂ a₃ : Site d}
    (hadj1 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁)
    (hadj2 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂)
    (hadj3 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₃).Infinite)
    (hcd12 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₂)
    (hcd13 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₃)
    (hcd23 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₂ ≠
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) :
    ω ∈ CorridorWorks a₁ a₂ a₃ W :=
  ⟨⟨bc8_arm_ne_of_cut_ne hcd12, bc8_arm_ne_of_cut_ne hcd13, bc8_arm_ne_of_cut_ne hcd23⟩,
   ⟨openSubgraph_le (forceOpenFinset W ω) hadj1, openSubgraph_le (forceOpenFinset W ω) hadj2,
     openSubgraph_le (forceOpenFinset W ω) hadj3⟩,
   ⟨hi1, hi2, hi3⟩, hcd12, hcd13, hcd23⟩


theorem bc8_threeMeetBox_subset_corridorCover (n : ℕ) (hrw : bc8_OriginRewiring d n) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G := by
  intro ω hω
  obtain ⟨W, _hW0, a₁, a₂, a₃, hadj1, hadj2, hadj3, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ := hrw ω hω
  refine Set.mem_iUnion.mpr ⟨a₁, Set.mem_iUnion.mpr ⟨a₂, Set.mem_iUnion.mpr ⟨a₃,
    Set.mem_iUnion.mpr ⟨W, ?_⟩⟩⟩⟩
  exact bc8_corridorWorks_of_rewiringData ω hadj1 hadj2 hadj3 hi1 hi2 hi3 hcd12 hcd13 hcd23


theorem bc8_hroute_of_originRewiring
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hrw : ∀ n : ℕ, bc8_OriginRewiring d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  hroute_of_corridorCover μ hfe (fun n => bc8_threeMeetBox_subset_corridorCover n (hrw n))


theorem bc8_burtonKeane_uniqueness_of_originRewiring
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hrw : ∀ n : ℕ, bc8_OriginRewiring d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_trif_route μ herg hfe bdry hbound hvol hdens
    (bc8_hroute_of_originRewiring μ hfe hrw)


theorem bc8_threeArmsNoCrossing_isCanonical (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ a₁ a₂ a₃ : Site d,
      (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃ ∧
      bc8_NoCrossing ω a₁ a₂ ∧ bc8_NoCrossing ω a₁ a₃ ∧ bc8_NoCrossing ω a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ :=
    bc8_threeArmClusters_distinct n ω hω
  exact ⟨a₁, a₂, a₃, hi1, hi2, hi3, hcd12, hcd13, hcd23,
    bc8_noCrossing ω a₁ a₂, bc8_noCrossing ω a₁ a₃, bc8_noCrossing ω a₂ a₃⟩


theorem bc8_bridge_nonvacuous (ω : ConfigSpace (Sym2 (Site d)))
    (h : ∃ a₁ a₂ a₃ : Site d,
      (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧ (openSubgraph d ω).Adj 0 a₃ ∧
      (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    IsCanonicalTrifurcation d ω 0 :=
  bc8_isCanonicalTrifurcation_of_originSplits ω h


end Walls
end StatMech
