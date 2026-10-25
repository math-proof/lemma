/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part9


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWFiniteRegion_start (T L : ℕ) (hT : 0 < T) :
    (hexAWFiniteRegion T L hT).start = hexAWStart := rfl

@[simp] theorem hexAWFiniteRegion_mids (T L : ℕ) (hT : 0 < T) :
    (hexAWFiniteRegion T L hT).mids = hexAWMids T L := rfl


theorem hexAWMids_reflect {T L : ℕ} {z : ℂ}
    (hz : z ∈ hexAWMids T L) :
    hsc_refl hexAWStart 4 z ∈ hexAWMids T L := by
  rw [hexAWMids, Finset.mem_biUnion] at hz ⊢
  obtain ⟨v, _, hv⟩ := hz
  rw [Finset.mem_image] at hv
  obtain ⟨e, _, rfl⟩ := hv
  refine ⟨hexAWReflectVertex v, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨hexAWReflectEdge e, Finset.mem_univ _, ?_⟩
  exact (hexAWMid_reflect v.1 e).symm

theorem hexAWFiniteRegion_reflect {T L : ℕ} (hT : 0 < T) (z : ℂ)
    (hz : (hexAWFiniteRegion T L hT).inRegion z) :
    (hexAWFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 4 z) := by
  change z ∈ hexAWMids T L at hz
  change hsc_refl hexAWStart 4 z ∈ hexAWMids T L
  exact hexAWMids_reflect hz


theorem hexAWFiniteRegion_reflect_one {T L : ℕ} (hT : 0 < T) (z : ℂ)
    (hz : (hexAWFiniteRegion T L hT).inRegion z) :
    (hexAWFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 1 z) := by
  rw [hexAW_refl_one_eq_four]
  exact hexAWFiniteRegion_reflect hT z hz


end
end StatMech.Universality
