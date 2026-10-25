/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

@[simp] theorem hexCSFiniteRegion_start (T L : ℕ) (hT : 0 < T) :
    (hexCSFiniteRegion T L hT).start = hexAWStart := rfl

@[simp] theorem hexCSFiniteRegion_mids (T L : ℕ) (hT : 0 < T) :
    (hexCSFiniteRegion T L hT).mids = hexCSMids T L := rfl

theorem hexCSMids_reflect {T L : ℕ} {z : ℂ}
    (hz : z ∈ hexCSMids T L) :
    hsc_refl hexAWStart 1 z ∈ hexCSMids T L := by
  rw [hexCSMids, Finset.mem_biUnion] at hz ⊢
  obtain ⟨v, _, hv⟩ := hz
  rw [Finset.mem_image] at hv
  obtain ⟨e, _, rfl⟩ := hv
  refine ⟨hexCSReflectVertex v, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨hexAWReflectEdge e, Finset.mem_univ _, ?_⟩
  rw [hexAW_refl_one_eq_four]
  exact (hexAWMid_reflect v.1 e).symm

theorem hexCSFiniteRegion_reflect {T L : ℕ} (hT : 0 < T) (z : ℂ)
    (hz : (hexCSFiniteRegion T L hT).inRegion z) :
    (hexCSFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 1 z) := by
  change z ∈ hexCSMids T L at hz
  change hsc_refl hexAWStart 1 z ∈ hexCSMids T L
  exact hexCSMids_reflect hz


end
end StatMech.Universality
