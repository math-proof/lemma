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
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc8_isCanonicalTrifurcation_of_arms (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ : Site d}
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧
      (openSubgraph d ω).Adj 0 a₃)
    (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite)
    (hcd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hcd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hcd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    IsCanonicalTrifurcation d ω 0 := by
  refine ⟨a₁, a₂, a₃, hne, hadj, hinf, ?_, ?_, ?_⟩
  · exact bc8_cut_ne_iff_disconnected.mp hcd12
  · exact bc8_cut_ne_iff_disconnected.mp hcd13
  · exact bc8_cut_ne_iff_disconnected.mp hcd23


theorem bc8_arm_ne_of_cut_ne {ω : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (h : cluster d (removeSite 0 ω) a ≠ cluster d (removeSite 0 ω) b) : a ≠ b := by
  rintro rfl; exact h rfl


theorem bc8_isCanonicalTrifurcation_of_threeArms (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ : Site d}
    (hadj1 : (openSubgraph d ω).Adj 0 a₁) (hadj2 : (openSubgraph d ω).Adj 0 a₂)
    (hadj3 : (openSubgraph d ω).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hcd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hcd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hcd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    IsCanonicalTrifurcation d ω 0 :=
  bc8_isCanonicalTrifurcation_of_arms ω
    ⟨bc8_arm_ne_of_cut_ne hcd12, bc8_arm_ne_of_cut_ne hcd13, bc8_arm_ne_of_cut_ne hcd23⟩
    ⟨hadj1, hadj2, hadj3⟩ ⟨hi1, hi2, hi3⟩ hcd12 hcd13 hcd23


theorem bc8_isCanonicalTrifurcation_of_originSplits (ω : ConfigSpace (Sym2 (Site d)))
    (h : ∃ a₁ a₂ a₃ : Site d,
      (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧ (openSubgraph d ω).Adj 0 a₃ ∧
      (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    IsCanonicalTrifurcation d ω 0 := by
  obtain ⟨a₁, a₂, a₃, hadj1, hadj2, hadj3, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ := h
  exact bc8_isCanonicalTrifurcation_of_threeArms ω hadj1 hadj2 hadj3 hi1 hi2 hi3 hcd12 hcd13 hcd23


end Walls
end StatMech
